// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

pub mod codegen;
pub mod context;
pub mod error;
pub mod function;
pub mod mangle;
pub mod types;

use inkwell::context::Context;
use move_binary_format::CompiledModule;
use move_stackless_bytecode::stackless_bytecode_generator::StacklessBytecodeGenerator;

use crate::codegen::{add_symbol_aliases, emit_assembly, run_optimization_passes};
use crate::context::LlvmContext;
use crate::error::CompileError;
use crate::function::{compile_function, declare_function};

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
    compile_module_with_deps(module, &[])
}

/// Compile a Move module to AArch64 assembly, with dependency modules visible
/// for resolving cross-module (e.g. native) function signatures.
///
/// Dependencies are included in the model but only functions from the target
/// module are compiled. Native functions in deps are declared as externs.
pub fn compile_module_with_deps(
    module: &CompiledModule,
    deps: &[CompiledModule],
) -> Result<String, CompileError> {
    let context = Context::create();
    let ctx = LlvmContext::new(&context, "move_module");

    // Build model: deps first, then target module (last).
    let all_modules: Vec<&CompiledModule> = deps.iter().chain(std::iter::once(module)).collect();
    let env = move_model::run_bytecode_model_builder(all_modules)
        .map_err(|e| CompileError::ModelBuilder(e.to_string()))?;

    // Only compile functions from the target module (the last one).
    let target_module_env = env.get_modules().last().unwrap();

    let funcs: Vec<_> = target_module_env
        .into_functions()
        .filter(|f| !f.is_native() && f.get_type_parameter_count() == 0)
        .map(|func_env| {
            let generator = StacklessBytecodeGenerator::new(&func_env);
            let func_data = generator.generate_function();
            (func_env, func_data)
        })
        .collect();

    // Pass 1: declare all functions (so callees are visible).
    let declarations: Vec<_> = funcs
        .iter()
        .map(|(func_env, func_data)| declare_function(&ctx, &env, func_env, func_data))
        .collect::<Result<_, _>>()?;

    // Pass 2: compile function bodies.
    for ((func_env, func_data), function) in funcs.iter().zip(declarations) {
        compile_function(&ctx, &env, function, func_env, func_data)?;
    }

    run_optimization_passes(&ctx.module)?;

    let asm = emit_assembly(&ctx.module)?;
    Ok(add_symbol_aliases(&asm))
}
