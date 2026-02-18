// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Error types for gas instrumentation.

use thiserror::Error;

/// Error during label resolution.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ResolveError {
    /// Labels at end of file with no following instruction.
    #[error("trailing labels with no instruction: {0:?}")]
    TrailingLabels(Vec<String>),
    /// Branch references an undefined label.
    #[error("undefined label '{label}' referenced at line {line}")]
    UndefinedLabel {
        /// The undefined label name.
        label: String,
        /// Line number where the reference occurs.
        line: usize,
    },
}

/// Errors that can occur during instrumentation.
#[derive(Debug, Error)]
pub enum InstrumentError {
    #[error("exceeded maximum label generation attempts ({max})")]
    LabelGenerationExhausted { max: usize },
}
