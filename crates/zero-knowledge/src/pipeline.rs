// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! End-to-end compilation pipeline: Move bytecode → SP1-compatible ELF.

use std::path::Path;

use inkwell::context::Context;
use move_binary_format::CompiledModule;

use compiler::{ModuleInfo, Target};

use sp1_sdk::SP1Stdin;

use crate::error::{ZkError, ZkResult};
use crate::linker::Linker;
use crate::proof::{Proof, Prover};
use crate::sp1::Sp1Commit;
use crate::stub::StubGenerator;

/// Result of compiling a Move function into an SP1-ready ELF.
pub struct CompiledElf {
    /// The raw ELF bytes.
    pub elf_bytes: Vec<u8>,
    /// Number of parameters.
    pub arg_count: usize,
    /// Number of u64 return values (0 or 1).
    pub ret_count: usize,
}

impl CompiledElf {
    /// Read a `.mv` file, deserialize it, and compile a function into an
    /// SP1-compatible ELF.
    pub fn from_file(path: impl AsRef<Path>, function_name: &str) -> ZkResult<Self> {
        let bytecode = std::fs::read(path).map_err(ZkError::Io)?;
        let module = CompiledModule::deserialize_with_defaults(&bytecode)
            .map_err(|e| ZkError::Function(e.to_string()))?;
        Self::compile(&module, function_name, &[])
    }

    /// Compile a Move module's function into an SP1-compatible ELF.
    ///
    /// Runs the full pipeline: find function → generate stub → compile to
    /// RISC-V → link relocations → build ELF.
    pub fn compile(
        module: &CompiledModule,
        function_name: &str,
        deps: &[CompiledModule],
    ) -> ZkResult<Self> {
        let info = ModuleInfo::from_module(module)?;
        let function = info
            .function(function_name)
            .ok_or_else(|| ZkError::Function(format!("function '{function_name}' not found")))?;

        let context = Context::create();
        let compiler = compiler::Compiler::new(&Target::Riscv64, &context, module, deps)?;
        let commit = compiler.inject_function(
            Sp1Commit::SYMBOL,
            Sp1Commit::signature(&context),
            |injected, function| Sp1Commit::new(injected).build(function),
        )?;
        let stub_asm = StubGenerator::from(function)
            .with_commit(&commit)
            .generate();
        compiler.set_module_assembly(&stub_asm);
        let object = compiler.emit_object()?;
        let elf_bytes = Linker::new(&object, "_start").link()?.build_elf()?;

        Ok(Self {
            elf_bytes,
            arg_count: function.arg_count,
            ret_count: function.ret_count,
        })
    }

    /// Prove execution with the given u64 inputs.
    ///
    /// If `mock` is true, uses the fast mock prover (no real proof).
    /// Otherwise uses the CPU prover.
    pub async fn prove(&self, inputs: &[u64], mock: bool) -> ZkResult<Proof> {
        if inputs.len() != self.arg_count {
            return Err(ZkError::Sp1(format!(
                "expected {} inputs, got {}",
                self.arg_count,
                inputs.len()
            )));
        }
        let elf = sp1_sdk::Elf::from(self.elf_bytes.clone());
        let mut stdin = SP1Stdin::new();
        for val in inputs {
            stdin.write(val);
        }
        if mock {
            Prover::mock().await.prove(elf, stdin, self.ret_count).await
        } else {
            Prover::cpu().await.prove(elf, stdin, self.ret_count).await
        }
    }
}

#[cfg(test)]
mod tests {
    use compiler::module::CompiledModuleBuilder;

    use super::CompiledElf;

    #[test]
    fn compile_produces_a_valid_elf() {
        let elf = CompiledElf::compile(&CompiledModuleBuilder::add(), "add", &[]).unwrap();
        assert_eq!(elf.arg_count, 2);
        assert_eq!(elf.ret_count, 1);
        assert!(!elf.elf_bytes.is_empty());
        assert_eq!(&elf.elf_bytes[..4], b"\x7fELF", "ELF magic");
    }

    #[test]
    fn compile_errors_on_unknown_function() {
        assert!(CompiledElf::compile(&CompiledModuleBuilder::add(), "nope", &[]).is_err());
    }

    #[tokio::test]
    async fn prove_rejects_a_wrong_input_count() {
        // `add` takes 2 args; the guard must reject before touching SP1.
        let elf = CompiledElf::compile(&CompiledModuleBuilder::add(), "add", &[]).unwrap();
        assert!(elf.prove(&[1], true).await.is_err());
    }
}
