//! Error types for native code verification

use thiserror::Error;

/// Errors discovered during verification
#[derive(Debug, Clone, Error)]
pub enum VerificationError {
    #[error("disallowed instruction at {offset:#x}: {mnemonic} ({reason})")]
    DisallowedInstruction {
        offset: usize,
        mnemonic: String,
        reason: String,
    },

    #[error("indirect branch at {offset:#x}: {mnemonic}")]
    IndirectBranch { offset: usize, mnemonic: String },

    #[error("invalid x23 modification at {offset:#x}: {mnemonic} (only gas decrements allowed)")]
    InvalidGasModification { offset: usize, mnemonic: String },

    #[error("missing gas check before back-edge at {back_edge_offset:#x} (target: {target_offset:#x})")]
    MissingGasCheck {
        back_edge_offset: usize,
        target_offset: usize,
    },

    #[error("malformed gas check at {offset:#x}: {reason}")]
    MalformedGasCheck { offset: usize, reason: String },

    #[error("invalid branch target at {branch_offset:#x}: target {target:#x} is not an instruction boundary")]
    InvalidBranchTarget { branch_offset: usize, target: usize },

    #[error("unreachable code at {offset:#x}")]
    UnreachableCode { offset: usize },
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

    /// Consumes the result and returns the errors
    pub fn into_errors(self) -> Vec<VerificationError> {
        self.errors
    }

    pub(crate) fn extend(&mut self, errors: impl IntoIterator<Item = VerificationError>) {
        self.errors.extend(errors);
    }
}