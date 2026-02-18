pub mod codegen;
pub mod context;
pub mod error;
pub mod function;
pub mod types;

use inkwell::context::Context;
use move_binary_format::CompiledModule;

use crate::codegen::{add_symbol_aliases, emit_assembly, run_optimization_passes};
use crate::context::LlvmContext;
use crate::error::CompileError;
use crate::function::lower_function;

/// Compile a serialized Move module to AArch64 assembly.
///
/// The input is raw Move bytecode (a serialized `CompiledModule`).
/// Returns assembly text suitable for feeding into `gas-instrument`.
pub fn compile(bytecode: &[u8]) -> Result<String, CompileError> {
    let module = CompiledModule::deserialize_with_defaults(bytecode)
        .map_err(|e| CompileError::Deserialize(e.to_string()))?;

    compile_module(&module)
}

/// Compile an already-deserialized Move module to AArch64 assembly.
pub fn compile_module(module: &CompiledModule) -> Result<String, CompileError> {
    let context = Context::create();
    let ctx = LlvmContext::new(&context, "move_module");

    for func_def in &module.function_defs {
        lower_function(&ctx, module, func_def)?;
    }

    run_optimization_passes(&ctx.module)?;

    let asm = emit_assembly(&ctx.module)?;
    Ok(add_symbol_aliases(&asm))
}
