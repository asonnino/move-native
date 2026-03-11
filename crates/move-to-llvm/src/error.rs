// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use move_model::ty::Type;
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Constant, Operation};
use thiserror::Error;

/// Convenience alias used throughout the crate.
pub type CompileResult<T> = Result<T, CompileError>;

#[derive(Debug, Error)]
pub enum CompileError {
    #[error("unsupported bytecode: {0:?}")]
    UnsupportedBytecode(Box<Bytecode>),

    #[error("unsupported type: {0:?}")]
    UnsupportedType(Box<Type>),

    #[error("unsupported constant: {0:?}")]
    UnsupportedConstant(Box<Constant>),

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
    UnsupportedOperation(Box<Operation>),

    #[error("model builder failed: {0}")]
    ModelBuilder(String),
}

impl CompileError {
    pub(crate) fn unsupported_bytecode(bc: Bytecode) -> Self {
        Self::UnsupportedBytecode(Box::new(bc))
    }

    pub(crate) fn unsupported_type(ty: Type) -> Self {
        Self::UnsupportedType(Box::new(ty))
    }

    pub(crate) fn unsupported_constant(c: Constant) -> Self {
        Self::UnsupportedConstant(Box::new(c))
    }

    pub(crate) fn unsupported_operation(op: Operation) -> Self {
        Self::UnsupportedOperation(Box::new(op))
    }

    pub(crate) fn llvm(msg: impl Into<String>) -> Self {
        Self::Llvm(msg.into())
    }

    pub(crate) fn target_init(msg: impl Into<String>) -> Self {
        Self::TargetInit(msg.into())
    }

    pub(crate) fn target_machine(msg: impl Into<String>) -> Self {
        Self::TargetMachine(msg.into())
    }

    pub(crate) fn codegen(msg: impl Into<String>) -> Self {
        Self::CodeGeneration(msg.into())
    }

    pub(crate) fn deserialize(msg: impl Into<String>) -> Self {
        Self::Deserialize(msg.into())
    }

    pub(crate) fn model_builder(msg: impl Into<String>) -> Self {
        Self::ModelBuilder(msg.into())
    }
}
