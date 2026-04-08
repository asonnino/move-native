// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! LLVM codegen backend: optimization, assembly emission, and object emission.

use inkwell::OptimizationLevel;
use inkwell::module::Module;
use inkwell::passes::PassBuilderOptions;
use inkwell::targets::{CodeModel, FileType, RelocMode, TargetMachine, TargetTriple};

use crate::assembly::Assembly;
use crate::error::{CompileError, CompileResult};
use crate::object_file::ObjectFile;
use crate::target::{CPU, Target};

/// Owns the LLVM `TargetMachine` and drives optimization and code emission.
pub(crate) struct CodegenBackend {
    machine: TargetMachine,
    check_gas_register: bool,
}

impl CodegenBackend {
    pub(crate) fn new(target: &Target) -> CompileResult<Self> {
        target.initialize();

        let triple = TargetTriple::create(target.triple());
        let llvm_target = inkwell::targets::Target::from_triple(&triple)
            .map_err(|e| CompileError::target_init(e.to_string()))?;

        let machine = llvm_target
            .create_target_machine(
                &triple,
                CPU,
                target.features(),
                OptimizationLevel::Default,
                RelocMode::PIC,
                CodeModel::Default,
            )
            .ok_or_else(|| CompileError::target_machine("failed to create target machine"))?;

        let check_gas_register = target.check_gas_register();
        Ok(Self {
            machine,
            check_gas_register,
        })
    }

    /// Run optimization passes on the module using the new pass manager.
    ///
    /// Runs mem2reg (promote allocas to SSA registers), instcombine, and
    /// simplifycfg — enough to clean up the alloca-heavy IR we generate.
    pub(crate) fn optimize(&self, module: &Module<'_>) -> CompileResult<()> {
        let options = PassBuilderOptions::create();
        module
            .run_passes(
                "mem2reg,instcombine<max-iterations=2>,simplifycfg",
                &self.machine,
                options,
            )
            .map_err(|e| CompileError::llvm(e.to_string()))
    }

    /// Emit the module as an ELF object file (`.o`).
    pub(crate) fn build_object(&self, module: &Module<'_>) -> CompileResult<ObjectFile> {
        let buf = self
            .machine
            .write_to_memory_buffer(module, FileType::Object)
            .map_err(|e| CompileError::codegen(e.to_string()))?;
        Ok(ObjectFile::new(buf.as_slice().to_vec()))
    }

    /// Emit the module as assembly text.
    pub(crate) fn build_assembly(&self, module: &Module<'_>) -> CompileResult<Assembly> {
        let buf = self
            .machine
            .write_to_memory_buffer(module, FileType::Assembly)
            .map_err(|e| CompileError::codegen(e.to_string()))?;

        let asm = std::str::from_utf8(buf.as_slice())
            .map_err(|e| CompileError::codegen(e.to_string()))?
            .to_string();

        if self.check_gas_register && Self::has_x23_misuse(&asm) {
            return Err(CompileError::codegen(
                "x23 (reserved for gas metering) used outside stp/ldp save/restore",
            ));
        }

        let mut assembly = Assembly::new(asm);
        assembly.strip_subsections();
        Ok(assembly)
    }

    /// Returns true if x23 appears in any instruction other than `stp`/`ldp`
    /// (callee-saved save/restore in function prologues/epilogues).
    fn has_x23_misuse(asm: &str) -> bool {
        for line in asm.lines() {
            let trimmed = line.trim();
            if !trimmed.contains("x23") {
                continue;
            }
            if trimmed.starts_with("stp\t")
                || trimmed.starts_with("ldp\t")
                || trimmed.starts_with("stp ")
                || trimmed.starts_with("ldp ")
                || trimmed.starts_with(';')
                || trimmed.starts_with('.')
                || trimmed.starts_with("//")
            {
                continue;
            }
            return true;
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::CodegenBackend;

    #[test]
    fn x23_in_stp_ldp_is_ok() {
        let asm = "stp\tx24, x23, [sp, #-16]!\nldp\tx24, x23, [sp], #16\n";
        assert!(!CodegenBackend::has_x23_misuse(asm));
    }

    #[test]
    fn x23_in_add_is_misuse() {
        let asm = "\tadd\tx23, x0, x1\n";
        assert!(CodegenBackend::has_x23_misuse(asm));
    }

    #[test]
    fn x23_in_comment_is_ok() {
        let asm = "; x23 is the gas register\n// x23 reserved\n";
        assert!(!CodegenBackend::has_x23_misuse(asm));
    }

    #[test]
    fn x23_in_directive_is_ok() {
        let asm = ".cfi_offset x23, -8\n";
        assert!(!CodegenBackend::has_x23_misuse(asm));
    }

    #[test]
    fn no_x23_is_ok() {
        let asm = "\tadd\tx0, x1, x2\n\tret\n";
        assert!(!CodegenBackend::has_x23_misuse(asm));
    }
}
