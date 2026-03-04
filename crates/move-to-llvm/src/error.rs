// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use move_model::ty::Type;
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Constant, Operation};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum CompileError {
    #[error("unsupported bytecode: {0:?}")]
    UnsupportedBytecode(Bytecode),

    #[error("unsupported type: {0:?}")]
    UnsupportedType(Type),

    #[error("unsupported constant: {0:?}")]
    UnsupportedConstant(Constant),

    #[error("function has no code unit")]
    NoCode,

    #[error("LLVM builder error: {0}")]
    Builder(#[from] inkwell::builder::BuilderError),

    #[error("LLVM error: {0}")]
    Llvm(String),

    #[error("failed to initialize target: {0}")]
    TargetInit(String),

    #[error("failed to create target machine: {0}")]
    TargetMachine(String),

    #[error("code generation failed: {0}")]
    CodeGeneration(String),

    #[error("failed to deserialize module: {0}")]
    Deserialize(String),

    #[error("unsupported operation: {0:?}")]
    UnsupportedOperation(Operation),

    #[error("model builder failed: {0}")]
    ModelBuilder(String),
}

/// Convenience alias used throughout the crate.
pub type CompileResult<T> = Result<T, CompileError>;
