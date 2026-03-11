// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

mod assembly;
mod compiler;
mod context;
mod error;
mod function;
mod mangle;
mod target;
mod types;

pub use assembly::Assembly;
pub use compiler::Compiler;
pub use error::{CompileError, CompileResult};
pub use target::Target;

/// Compile serialized Move bytecode to assembly.
///
/// Convenience wrapper around [`Compiler::compile`].
pub fn compile(target: &Target, bytecode: &[u8]) -> CompileResult<Assembly> {
    Compiler::compile(target, bytecode)
}

/// Compile an already-deserialized Move module to assembly.
///
/// Convenience wrapper around [`Compiler::compile_module`].
pub fn compile_module(
    target: &Target,
    module: &move_binary_format::CompiledModule,
) -> CompileResult<Assembly> {
    Compiler::compile_module(target, module)
}

/// Compile a Move module with dependency modules visible for resolving
/// cross-module function signatures.
///
/// Convenience wrapper around [`Compiler::compile_module_with_dependencies`].
pub fn compile_module_with_deps(
    target: &Target,
    module: &move_binary_format::CompiledModule,
    deps: &[move_binary_format::CompiledModule],
) -> CompileResult<Assembly> {
    Compiler::compile_module_with_dependencies(target, module, deps)
}
