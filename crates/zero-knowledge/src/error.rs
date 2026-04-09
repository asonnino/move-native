// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use thiserror::Error;

#[derive(Debug, Error)]
pub enum ZkError {
    #[error("compilation failed: {0}")]
    Compile(#[from] compiler::CompileError),

    #[error("linker error: {0}")]
    Linker(String),

    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error("function error: {0}")]
    Function(String),

    #[error("SP1 error: {0}")]
    Sp1(String),
}

pub type ZkResult<T> = Result<T, ZkError>;
