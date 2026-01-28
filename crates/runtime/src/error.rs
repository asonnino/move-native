//! Error types for the runtime crate

use std::path::PathBuf;

use thiserror::Error;

/// Result type alias for runtime operations
pub type RuntimeResult<T> = Result<T, RuntimeError>;

/// Runtime errors
#[derive(Debug, Clone, Error)]
pub enum RuntimeError {
    #[error("out of gas (initial gas: {initial_gas})")]
    OutOfGas { initial_gas: i64 },

    #[error("{}", display_load_error(path, reason))]
    LoadError { path: PathBuf, reason: String },

    #[error("module not found: {id}")]
    ModuleNotFound { id: String },

    #[error("function not found: {name}")]
    FunctionNotFound { name: String },

    #[error("code pool exhausted (all slots in use)")]
    PoolExhausted,

    #[error("failed to set up signal handler: {reason}")]
    SignalSetupError { reason: String },

    #[error("gas limit {limit} exceeds maximum supported value (i64::MAX)")]
    GasLimitTooLarge { limit: u64 },
}

/// Show full path in debug builds, filename only in release
fn display_load_error(path: &PathBuf, reason: &str) -> String {
    #[cfg(debug_assertions)]
    let path_display = path.display().to_string();

    #[cfg(not(debug_assertions))]
    let path_display = path
        .file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_else(|| "<unknown>".into());

    format!("failed to load module '{path_display}': {reason}")
}
