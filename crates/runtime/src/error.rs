//! Error types for the runtime crate

use std::path::PathBuf;
use thiserror::Error;

/// Runtime errors
#[derive(Debug, Clone, Error)]
pub enum RuntimeError {
    #[error("out of gas (initial gas: {initial_gas})")]
    OutOfGas { initial_gas: i64 },

    #[error("failed to load library at {path}: {reason}")]
    LoadError { path: PathBuf, reason: String },

    #[error("symbol not found: {symbol}")]
    SymbolNotFound { symbol: String },

    #[error("failed to set up signal handler: {reason}")]
    SignalSetupError { reason: String },

    #[error("gas limit {limit} exceeds maximum supported value (i64::MAX)")]
    GasLimitTooLarge { limit: u64 },
}

/// Result type alias for runtime operations
pub type RuntimeResult<T> = Result<T, RuntimeError>;
