// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::fmt;
use std::panic::{AssertUnwindSafe, catch_unwind};

use thiserror::Error;

#[derive(Debug, Error)]
pub enum CompileError {
    // Input errors (Move module or environment is wrong)
    #[error("unsupported: {0}")]
    Unsupported(String),

    #[error("not implemented: {0}")]
    NotImplemented(String),

    #[error("type mismatch: {0}")]
    TypeMismatch(String),

    #[error("invalid reference: {0}")]
    InvalidReference(String),

    #[error(
        "unresolved type parameter {0}: must be instantiated or appear only in phantom positions"
    )]
    UnresolvedTypeParam(u16),

    #[error("missing dependency: {0}")]
    MissingDependency(String),

    #[error("failed to deserialize module: {0}")]
    Deserialize(String),

    #[error("model builder failed: {0}")]
    ModelBuilder(String),

    #[error("internal compiler error: {0}")]
    Internal(String),

    // LLVM infrastructure errors
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

    // Context wrapper (preserves inner error kind)
    #[error("{context}: {source}")]
    Contextualized {
        context: String,
        source: Box<CompileError>,
    },
}

impl CompileError {
    pub(crate) fn not_implemented(val: impl fmt::Debug) -> Self {
        Self::NotImplemented(format!("{val:?}"))
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

    pub(crate) fn internal(msg: impl Into<String>) -> Self {
        Self::Internal(msg.into())
    }

    /// Wrap this error with additional context, preserving the original variant.
    pub fn context(self, ctx: impl fmt::Display) -> Self {
        Self::Contextualized {
            context: ctx.to_string(),
            source: Box::new(self),
        }
    }

    /// Peel away context layers to get the root cause.
    pub fn root_cause(&self) -> &CompileError {
        match self {
            Self::Contextualized { source, .. } => source.root_cause(),
            other => other,
        }
    }
}

/// Convenience alias used throughout the crate.
pub type CompileResult<T> = Result<T, CompileError>;

/// Extension trait for adding context to `CompileResult` via method chaining.
///
/// Defers formatting to the error path — the closure is only called on `Err`.
pub(crate) trait CompileContext<T> {
    fn with_context(self, f: impl FnOnce() -> String) -> CompileResult<T>;
}

impl<T> CompileContext<T> for CompileResult<T> {
    fn with_context(self, f: impl FnOnce() -> String) -> CompileResult<T> {
        self.map_err(|e| e.context(f()))
    }
}

/// Run `generate` inside `catch_unwind`, converting any panic into a
/// `CompileError::Internal`.
///
/// Used to guard calls into upstream crates (e.g. `StacklessBytecodeGenerator`)
/// that may panic on unexpected input.
pub(crate) fn catch_panic<T>(label: &str, generate: impl FnOnce() -> T) -> CompileResult<T> {
    catch_unwind(AssertUnwindSafe(generate)).map_err(|payload| {
        let payload = payload.as_ref();
        let detail = payload
            .downcast_ref::<&'static str>()
            .copied()
            .or_else(|| payload.downcast_ref::<String>().map(String::as_str))
            .unwrap_or("non-string panic payload");
        CompileError::internal(format!("upstream panic in '{label}': {detail}"))
    })
}

/// Checked cast of a bytecode-derived index to a u32 LLVM field index.
pub(crate) fn to_field_index(i: usize) -> CompileResult<u32> {
    u32::try_from(i).map_err(|_| CompileError::internal(format!("field index {i} exceeds u32")))
}

#[cfg(test)]
mod tests {
    use super::{CompileError, catch_panic};

    #[test]
    fn root_cause_no_context() {
        let err = CompileError::internal("boom");
        assert!(matches!(err.root_cause(), CompileError::Internal(msg) if msg == "boom"));
    }

    #[test]
    fn root_cause_single_wrap() {
        let err = CompileError::internal("inner").context("outer");
        assert!(matches!(err.root_cause(), CompileError::Internal(msg) if msg == "inner"));
    }

    #[test]
    fn root_cause_double_wrap() {
        let err = CompileError::internal("deep").context("mid").context("top");
        assert!(matches!(err.root_cause(), CompileError::Internal(msg) if msg == "deep"));
    }

    #[test]
    fn catch_panic_normal() {
        let result = catch_panic("test", || 42);
        assert_eq!(result.unwrap(), 42);
    }

    #[test]
    fn catch_panic_string_panic() {
        let result = catch_panic::<()>("test", || panic!("kaboom"));
        let err = result.unwrap_err();
        let msg = format!("{err}");
        assert!(
            msg.contains("kaboom"),
            "error should contain panic message: {msg}"
        );
        assert!(matches!(err, CompileError::Internal(_)));
    }
}
