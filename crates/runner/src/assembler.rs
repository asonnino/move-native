// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Assembles Arm64 assembly text into machine code with symbol extraction

use std::collections::HashMap;
use std::process::Command;

use object::{Object, ObjectSection, ObjectSymbol};

use crate::error::PipelineError;

/// Result of assembling an assembly source file
pub struct AssembledModule {
    /// Raw executable bytes from the text section
    pub code: Vec<u8>,
    /// Function name -> offset in code (leading `_` stripped on macOS)
    pub entry_points: HashMap<String, u32>,
}

/// Assemble Arm64 assembly source text into machine code.
///
/// Shells out to the platform `as` assembler, then parses the resulting
/// object file to extract the code section and symbol table.
pub fn assemble(source: &str) -> Result<AssembledModule, PipelineError> {
    let dir = tempfile::tempdir()?;
    let asm_path = dir.path().join("input.s");
    let obj_path = dir.path().join("output.o");

    std::fs::write(&asm_path, source)?;

    let output = Command::new("as")
        .args(["-o", obj_path.to_str().unwrap(), asm_path.to_str().unwrap()])
        .output()?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(PipelineError::AssemblerFailed(stderr.into_owned()));
    }

    let obj_data = std::fs::read(&obj_path)?;
    let file = object::File::parse(&*obj_data)
        .map_err(|e| PipelineError::AssemblerFailed(e.to_string()))?;

    let text_section = file
        .section_by_name("__text")
        .or_else(|| file.section_by_name(".text"))
        .ok_or(PipelineError::NoCodeSection)?;

    let section_index = text_section.index();
    let section_addr = text_section.address();
    let code = text_section
        .data()
        .map_err(|e| PipelineError::AssemblerFailed(e.to_string()))?
        .to_vec();

    // Extract symbols defined in the text section
    let mut entry_points = HashMap::new();
    for symbol in file.symbols() {
        if symbol.section_index() != Some(section_index) {
            continue;
        }
        if symbol.size() == 0 && symbol.address() == 0 && symbol.name() == Ok("") {
            continue; // skip null/file symbols
        }
        if let Ok(name) = symbol.name() {
            if name.is_empty() {
                continue;
            }
            // Strip leading underscore (macOS Mach-O convention)
            let canonical = name.strip_prefix('_').unwrap_or(name);
            let offset = (symbol.address() - section_addr) as u32;
            entry_points.insert(canonical.to_string(), offset);
        }
    }

    Ok(AssembledModule { code, entry_points })
}
