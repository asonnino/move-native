// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! ELF object file output from the compiler, with relocation support.

use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget, SymbolKind};

use crate::error::{CompileError, CompileResult};

/// Compiled object file (`.o` bytes) produced by [`Compiler::emit_object`].
///
/// Wraps the raw ELF relocatable object and provides methods to extract
/// linked code without needing an external linker.
pub struct ObjectFile(Vec<u8>);

impl ObjectFile {
    pub(crate) fn new(bytes: Vec<u8>) -> Self {
        Self(bytes)
    }

    /// Raw `.o` bytes.
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Extract the `.text` section with all internal relocations applied,
    /// plus the offset of a named entry-point symbol.
    ///
    /// This is a minimal in-process linker: it resolves PC-relative call
    /// relocations so the returned code bytes can be loaded directly.
    pub fn linked_text(&self, entry: &str) -> CompileResult<LinkedText> {
        let obj = object::File::parse(self.as_bytes())
            .map_err(|e| CompileError::codegen(format!("failed to parse object: {e}")))?;

        let text = obj
            .section_by_name(".text")
            .ok_or_else(|| CompileError::codegen("no .text section"))?;
        let text_index = text.index();
        let text_addr = text.address();
        let mut code = text
            .data()
            .map_err(|e| CompileError::codegen(format!("failed to read .text: {e}")))?
            .to_vec();

        // Build symbol index → offset-in-.text map.
        let mut symbols: std::collections::HashMap<object::SymbolIndex, u64> =
            std::collections::HashMap::new();
        for sym in obj.symbols() {
            if sym.section_index() == Some(text_index) {
                symbols.insert(sym.index(), sym.address() - text_addr);
            }
        }

        // Apply relocations.
        for (offset, reloc) in text.relocations() {
            let target_offset = match reloc.target() {
                RelocationTarget::Symbol(sym_idx) => {
                    symbols.get(&sym_idx).copied().ok_or_else(|| {
                        let name = obj
                            .symbol_by_index(sym_idx)
                            .and_then(|s| s.name().map(|n| n.to_string()))
                            .unwrap_or_else(|_| "?".into());
                        CompileError::codegen(format!("unresolved symbol: {name}"))
                    })?
                }
                _ => return Err(CompileError::codegen("unsupported relocation target")),
            };

            let flags = reloc.flags();
            let is_call = matches!(
                flags,
                object::RelocationFlags::Elf {
                    r_type: object::elf::R_RISCV_CALL | object::elf::R_RISCV_CALL_PLT
                }
            );

            if is_call {
                apply_riscv_call(&mut code, offset, target_offset);
            } else {
                return Err(CompileError::codegen(format!(
                    "unsupported relocation at offset {offset:#x}: {flags:?}"
                )));
            }
        }

        // Find entry symbol.
        let entry_offset = obj
            .symbols()
            .find(|s| s.name() == Ok(entry) && s.kind() == SymbolKind::Text)
            .map(|s| s.address() - text_addr)
            .ok_or_else(|| CompileError::codegen(format!("symbol '{entry}' not found")))?;

        Ok(LinkedText { code, entry_offset })
    }
}

/// Relocated `.text` code ready for direct execution or ELF packaging.
pub struct LinkedText {
    /// Machine code bytes with all internal relocations resolved.
    pub code: Vec<u8>,
    /// Offset of the entry-point symbol within `code`.
    pub entry_offset: u64,
}

/// Apply a RISC-V CALL/CALL_PLT relocation: patch an auipc+jalr pair
/// with the PC-relative offset to the target.
fn apply_riscv_call(code: &mut [u8], offset: u64, target_offset: u64) {
    let rel = target_offset as i64 - offset as i64;

    let hi20 = ((rel + 0x800) >> 12) & 0xfffff;
    let lo12 = rel - (hi20 << 12);

    let off = offset as usize;
    let auipc = u32::from_le_bytes(code[off..off + 4].try_into().unwrap());
    let jalr = u32::from_le_bytes(code[off + 4..off + 8].try_into().unwrap());

    // auipc: imm[31:12] in bits [31:12]
    let auipc = (auipc & 0xfff) | ((hi20 as u32) << 12);
    // jalr: imm[11:0] in bits [31:20]
    let jalr = (jalr & 0xfffff) | ((lo12 as u32 & 0xfff) << 20);

    code[off..off + 4].copy_from_slice(&auipc.to_le_bytes());
    code[off + 4..off + 8].copy_from_slice(&jalr.to_le_bytes());
}
