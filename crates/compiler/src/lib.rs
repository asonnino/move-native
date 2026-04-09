// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

mod assembly;
mod codegen;
mod compiler;
mod context;
mod error;
mod function;
mod layout;
mod mangle;
pub mod module;
mod object_file;
mod target;
mod types;

pub use assembly::Assembly;
pub use compiler::Compiler;
pub use error::{CompileError, CompileResult};
pub use module::{FunctionInfo, ModuleInfo};
pub use object_file::ObjectFile;
pub use target::Target;

/// Compile serialized Move bytecode to assembly text.
///
/// Convenience wrapper: deserializes the bytecode and calls
/// [`Compiler::emit_assembly`].
pub fn compile(target: &Target, bytecode: &[u8]) -> CompileResult<Assembly> {
    let module = move_binary_format::CompiledModule::deserialize_with_defaults(bytecode)
        .map_err(|e| CompileError::deserialize(e.to_string()))?;
    compile_module(target, &module)
}

/// Compile an already-deserialized Move module to assembly text.
pub fn compile_module(
    target: &Target,
    module: &move_binary_format::CompiledModule,
) -> CompileResult<Assembly> {
    compile_module_with_deps(target, module, &[])
}

/// Compile a Move module to assembly text with dependency modules visible
/// for resolving cross-module function signatures.
pub fn compile_module_with_deps(
    target: &Target,
    module: &move_binary_format::CompiledModule,
    deps: &[move_binary_format::CompiledModule],
) -> CompileResult<Assembly> {
    let context = inkwell::context::Context::create();
    let compiler = Compiler::new(target, &context, module, deps)?;
    compiler.emit_assembly()
}
