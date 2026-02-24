// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

mod assembly;
pub mod compiler;
pub(crate) mod context;
pub mod error;
pub(crate) mod function;
mod mangle;
mod types;

pub use assembly::Assembly;
pub use compiler::Compiler;
pub use error::{CompileError, CompileResult};

/// Compile serialized Move bytecode to AArch64 assembly.
///
/// Convenience wrapper around [`Compiler::compile`].
pub fn compile(bytecode: &[u8]) -> CompileResult<Assembly> {
    Compiler::compile(bytecode)
}

/// Compile an already-deserialized Move module to AArch64 assembly.
///
/// Convenience wrapper around [`Compiler::compile_module`].
pub fn compile_module(module: &move_binary_format::CompiledModule) -> CompileResult<Assembly> {
    Compiler::compile_module(module)
}

/// Compile a Move module with dependency modules visible for resolving
/// cross-module function signatures.
///
/// Convenience wrapper around [`Compiler::compile_module_with_deps`].
pub fn compile_module_with_deps(
    module: &move_binary_format::CompiledModule,
    deps: &[move_binary_format::CompiledModule],
) -> CompileResult<Assembly> {
    Compiler::compile_module_with_deps(module, deps)
}
