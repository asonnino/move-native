// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::{fmt, ops::Deref};

use inkwell::OptimizationLevel;
use inkwell::module::Module;
use inkwell::passes::PassBuilderOptions;
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple,
};

use crate::error::{CompileError, CompileResult};

const CPU: &str = "generic";
/// Reserve x23 so LLVM never allocates the gas register.
const FEATURES: &str = "+reserve-x23";

/// LLVM target triple for the host platform.
#[cfg(target_os = "macos")]
const HOST_TRIPLE: &str = "aarch64-apple-darwin";
#[cfg(not(target_os = "macos"))]
const HOST_TRIPLE: &str = "aarch64-unknown-linux-gnu";

/// AArch64 assembly output from the compiler.
pub struct Assembly(String);

impl Assembly {
    /// Post-process: add platform-compatible symbol aliases and strip
    /// `.subsections_via_symbols`.
    ///
    /// On macOS (where LLVM emits `_name` symbols), adds unprefixed aliases
    /// so that instrumenter and the runtime can find functions by their
    /// Move names. On Linux, adds underscore-prefixed aliases for the same
    /// cross-platform compatibility.
    ///
    /// Also strips `.subsections_via_symbols` — Mach-O's dead-stripping
    /// directive that prevents the assembler from encoding `tbz`/`tbnz`
    /// branch-to-label (the assembler can't guarantee range when subsections
    /// may be reordered).
    pub fn add_symbol_aliases(&mut self) {
        let asm = &self.0;
        let mut output = String::with_capacity(asm.len());
        let mut global_names: Vec<&str> = Vec::new();

        for line in asm.lines() {
            let trimmed = line.trim();
            if let Some(name) = trimmed
                .strip_prefix(".globl\t")
                .or_else(|| trimmed.strip_prefix(".globl "))
            {
                let name = name.trim();
                global_names.push(name);
            }
        }

        // Strip .subsections_via_symbols to allow tbz/tbnz with local labels
        for line in asm.lines() {
            if line.trim() == ".subsections_via_symbols" {
                continue;
            }
            output.push_str(line);
            output.push('\n');
        }

        if !global_names.is_empty() {
            output.push('\n');
            for name in &global_names {
                if let Some(bare) = name.strip_prefix('_') {
                    // macOS: _add exists, add alias for bare name
                    output.push_str(&format!(".globl {bare}\n"));
                    output.push_str(&format!("{bare}:\n"));
                    output.push_str(&format!("\tb {name}\n"));
                } else {
                    // Linux: add exists, add alias for _name
                    output.push_str(&format!(".globl _{name}\n"));
                    output.push_str(&format!("_{name}:\n"));
                    output.push_str(&format!("\tb {name}\n"));
                }
            }
        }

        self.0 = output;
    }
}

impl AsRef<[u8]> for Assembly {
    fn as_ref(&self) -> &[u8] {
        self.0.as_bytes()
    }
}

impl Deref for Assembly {
    type Target = str;

    fn deref(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Assembly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Owns the LLVM `TargetMachine` and drives optimization and assembly emission.
pub(crate) struct AssemblyBuilder {
    machine: TargetMachine,
}

impl AssemblyBuilder {
    pub fn new() -> CompileResult<Self> {
        Target::initialize_aarch64(&InitializationConfig::default());

        let triple = TargetTriple::create(HOST_TRIPLE);
        let target =
            Target::from_triple(&triple).map_err(|e| CompileError::TargetInit(e.to_string()))?;

        let machine = target
            .create_target_machine(
                &triple,
                CPU,
                FEATURES,
                OptimizationLevel::Default,
                RelocMode::PIC,
                CodeModel::Default,
            )
            .ok_or_else(|| CompileError::TargetMachine("failed to create target machine".into()))?;

        Ok(Self { machine })
    }

    /// Run optimization passes on the module using the new pass manager.
    ///
    /// Runs mem2reg (promote allocas to SSA registers), instcombine, and
    /// simplifycfg — enough to clean up the alloca-heavy IR we generate.
    pub fn optimize(&self, module: &Module<'_>) -> CompileResult<()> {
        let options = PassBuilderOptions::create();
        module
            .run_passes("mem2reg,instcombine,simplifycfg", &self.machine, options)
            .map_err(|e| CompileError::Llvm(e.to_string()))
    }

    /// Emit the module as AArch64 assembly text.
    pub fn emit_assembly(&self, module: &Module<'_>) -> CompileResult<Assembly> {
        let buf = self
            .machine
            .write_to_memory_buffer(module, FileType::Assembly)
            .map_err(|e| CompileError::CodeGeneration(e.to_string()))?;

        let asm = std::str::from_utf8(buf.as_slice())
            .map_err(|e| CompileError::CodeGeneration(e.to_string()))?
            .to_string();

        Ok(Assembly(asm))
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;

    use super::Assembly;

    #[test]
    fn macos_symbols_get_bare_alias() {
        let mut asm = Assembly(
            indoc! {"
                .globl\t_foo
                _foo:
                \tmov x0, #42
                \tret
            "}
            .into(),
        );
        asm.add_symbol_aliases();
        assert!(asm.contains(".globl foo\n"));
        assert!(asm.contains("foo:\n\tb _foo\n"));
    }

    #[test]
    fn linux_symbols_get_underscore_alias() {
        let mut asm = Assembly(
            indoc! {"
                .globl\tfoo
                foo:
                \tmov x0, #42
                \tret
            "}
            .into(),
        );
        asm.add_symbol_aliases();
        assert!(asm.contains(".globl _foo\n"));
        assert!(asm.contains("_foo:\n\tb foo\n"));
    }

    #[test]
    fn strips_subsections_via_symbols() {
        let mut asm = Assembly(
            indoc! {"
                .globl\t_foo
                _foo:
                \tret
                .subsections_via_symbols
            "}
            .into(),
        );
        asm.add_symbol_aliases();
        assert!(!asm.contains("subsections_via_symbols"));
    }

    #[test]
    fn no_globals_no_alias_section() {
        let mut asm = Assembly(
            indoc! {"
                ; just a comment
                \tmov x0, #1
                \tret
            "}
            .into(),
        );
        asm.add_symbol_aliases();
        assert!(!asm.contains(".globl"));
        assert!(!asm.contains("\tb "));
    }

    #[test]
    fn multiple_globals_produce_multiple_aliases() {
        let mut asm = Assembly(
            indoc! {"
                .globl\t_alpha
                .globl\t_beta
                _alpha:
                \tret
                _beta:
                \tret
            "}
            .into(),
        );
        asm.add_symbol_aliases();
        assert!(asm.contains(".globl alpha\n"));
        assert!(asm.contains("alpha:\n\tb _alpha\n"));
        assert!(asm.contains(".globl beta\n"));
        assert!(asm.contains("beta:\n\tb _beta\n"));
    }
}
