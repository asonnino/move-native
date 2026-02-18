// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

pub mod codegen;
pub mod context;
pub mod error;
pub mod function;
pub mod types;

use inkwell::context::Context;
use move_binary_format::CompiledModule;
use move_stackless_bytecode::stackless_bytecode_generator::StacklessBytecodeGenerator;

use crate::codegen::{add_symbol_aliases, emit_assembly, run_optimization_passes};
use crate::context::LlvmContext;
use crate::error::CompileError;
use crate::function::lower_function;

/// Compile a serialized Move module to AArch64 assembly.
///
/// The input is raw Move bytecode (a serialized `CompiledModule`).
/// Returns assembly text suitable for feeding into `instrumenter`.
pub fn compile(bytecode: &[u8]) -> Result<String, CompileError> {
    let module = CompiledModule::deserialize_with_defaults(bytecode)
        .map_err(|e| CompileError::Deserialize(e.to_string()))?;

    compile_module(&module)
}

/// Compile an already-deserialized Move module to AArch64 assembly.
pub fn compile_module(module: &CompiledModule) -> Result<String, CompileError> {
    let context = Context::create();
    let ctx = LlvmContext::new(&context, "move_module");

    let env = move_model::run_bytecode_model_builder([module])
        .map_err(|e| CompileError::ModelBuilder(e.to_string()))?;

    for module_env in env.get_modules() {
        for func_env in module_env.into_functions() {
            if func_env.is_native() {
                continue;
            }
            let generator = StacklessBytecodeGenerator::new(&func_env);
            let func_data = generator.generate_function();
            lower_function(&ctx, &func_env, &func_data)?;
        }
    }

    run_optimization_passes(&ctx.module)?;

    let asm = emit_assembly(&ctx.module)?;
    Ok(add_symbol_aliases(&asm))
}
