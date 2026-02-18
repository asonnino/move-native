//! Error types for native code verification

use std::ops::Range;

use thiserror::Error;

/// Errors that can occur during decoding
#[derive(Debug, Error)]
pub enum DecodeError {
    #[error("failed to decode instruction at offset {offset:#x}: {message}")]
    InvalidInstruction { offset: usize, message: String },

    #[error("code section size {size} is not aligned to 4 bytes (corrupted binary?)")]
    UnalignedCode { size: usize },
}

/// Errors discovered during verification
#[derive(Debug, Clone, Error)]
pub enum VerificationError {
    #[error("disallowed instruction at {offset:#x}: {mnemonic} ({reason})")]
    DisallowedInstruction {
        offset: usize,
        mnemonic: String,
        reason: String,
    },

    #[error("invalid x23 usage at {offset:#x}: {mnemonic} (only gas decrements may touch x23)")]
    InvalidGasRegisterUsage { offset: usize, mnemonic: String },

    #[error(
        "missing gas check before back-edge at {back_edge_offset:#x} (target: {target_offset:#x})"
    )]
    MissingGasCheck {
        back_edge_offset: usize,
        target_offset: usize,
    },

    #[error(
        "gas sequence before back-edge at {back_edge_offset:#x}: expected '{expected}' at {position_offset:#x}, found '{found}'"
    )]
    GasSequenceUnexpectedInstruction {
        back_edge_offset: usize,
        position_offset: usize,
        expected: &'static str,
        found: String,
    },

    #[error(
        "gas sequence before back-edge at {back_edge_offset:#x}: tbz at {tbz_offset:#x} targets {actual_target:#x}, expected {expected_target:#x}"
    )]
    GasSequenceBadTarget {
        back_edge_offset: usize,
        tbz_offset: usize,
        actual_target: usize,
        expected_target: usize,
    },

    #[error(
        "branch at {branch_offset:#x} targets inside gas check sequence at {target_offset:#x}"
    )]
    BranchIntoGasSequence {
        branch_offset: usize,
        target_offset: usize,
    },

    #[error(
        "invalid branch target at {branch_offset:#x}: target {target:#x} is not an instruction boundary"
    )]
    InvalidBranchTarget { branch_offset: usize, target: usize },

    #[error("unreachable code at {offset:#x?}")]
    UnreachableCode { offset: Range<usize> },

    #[error("stack depth {max_depth} bytes exceeds budget of {budget} bytes")]
    StackDepthExceeded { max_depth: u64, budget: u64 },

    #[error("recursive call graph detected at function {cycle_entry:#x}")]
    RecursiveCallGraph { cycle_entry: usize },

    #[error("unbounded SP modification at {offset:#x}: {mnemonic}")]
    UnsafeStackModification { offset: usize, mnemonic: String },
}

/// Result of verification containing any errors found
#[derive(Debug, Default)]
pub struct VerificationResult {
    errors: Vec<VerificationError>,
}

impl VerificationResult {
    /// Returns true if verification passed with no errors
    pub fn is_ok(&self) -> bool {
        self.errors.is_empty()
    }

    /// Returns the list of verification errors
    pub fn errors(&self) -> &[VerificationError] {
        &self.errors
    }

    pub(crate) fn extend(&mut self, errors: impl IntoIterator<Item = VerificationError>) {
        self.errors.extend(errors);
    }
}
