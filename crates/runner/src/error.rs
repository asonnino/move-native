// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Unified error type for the compilation pipeline

use thiserror::Error;

/// Errors that can occur during the compilation pipeline
#[derive(Debug, Error)]
pub enum PipelineError {
    #[error("compilation failed: {0}")]
    Compile(#[from] compiler::CompileError),

    #[error("label resolution failed: {0}")]
    Resolve(#[from] instrumenter::ResolveError),

    #[error("instrumentation failed: {0}")]
    Instrument(#[from] instrumenter::InstrumentError),

    #[error("assembler failed: {0}")]
    AssemblerFailed(String),

    #[error("no code section in assembled output")]
    NoCodeSection,

    #[error("decode failed: {0}")]
    Decode(#[from] verifier::DecodeError),

    #[error("verification failed with {} error(s)", .0.len())]
    Verification(Vec<verifier::VerificationError>),

    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
}
