//! Gas instrumentation for Arm64 assembly
//!
//! This crate provides tools to:
//! - Parse Arm64 assembly text files
//! - Build a control flow graph (CFG)
//! - Detect back-edges (loops)
//! - Insert gas metering sequences at back-edges
//!
//! Based on the DeCl paper: "Deterministic Client: Enforcing Determinism on Untrusted Machine Code"

pub mod cfg;
pub mod instrument;
pub mod parser;

pub use cfg::{build as build_cfg, Cfg};
pub use instrument::instrument;
pub use parser::{parse, Directive, Instruction, ParsedLine};
