//! Gas instrumentation for Arm64 assembly
//!
//! This crate provides tools to:
//! - Parse Arm64 assembly text files
//! - Build a control flow graph (CFG)
//! - Detect back-edges (loops)
//! - Insert gas metering sequences at back-edges
//!
//! Based on the DeCl paper: "Deterministic Client: Enforcing Determinism on Untrusted Machine Code"

pub mod instrument;
pub mod parser;

pub use cfg::BlockIndex;
pub use instrument::{instrument, InstrumentError};
pub use parser::{
    ParsedAssembly,
    ParsedLine,
    ResolveError,
    ResolvedInstruction,
    Statement,
    UnresolvedInstruction,
};

/// Result of building a CFG from parsed assembly
pub struct CfgResult {
    /// The control flow graph
    pub cfg: cfg::Cfg,
    /// The resolved instructions (for mapping back to line numbers)
    pub resolved: Vec<ResolvedInstruction>,
}

/// Build a CFG from parsed assembly
///
/// This resolves labels to instruction indices, then builds the CFG.
/// Returns the CFG and resolved instructions (needed to map instruction
/// indices back to line numbers for instrumentation).
///
/// Returns an error if label resolution fails (undefined labels, trailing labels).
pub fn build_cfg(asm: &ParsedAssembly<'_>) -> Result<CfgResult, ResolveError> {
    let resolved = asm.resolve()?;
    let cfg = cfg::build_cfg(&resolved);
    Ok(CfgResult { cfg, resolved })
}
