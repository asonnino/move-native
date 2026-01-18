//! Control Flow Graph analysis for Arm64
//!
//! This crate provides:
//! - **CFG construction** from instruction sequences (text or binary)
//! - **Back-edge detection** using dominator analysis
//! - **Arm64 opcode classification** for control flow and verification
//!
//! # Architecture
//!
//! The CFG builder is generic over instruction types via the [`InstructionInfo`] trait.
//! Both text assembly (gas-instrument) and binary (native-verifier) implement this trait:
//!
//! - Text assembly: `ResolvedInstruction` (instruction indices after label resolution)
//! - Binary: `DecodedInstruction` (byte offsets)
//!
//! # Modules
//!
//! - [`arm64`]: Opcode classification and whitelist checking
//! - [`traits`]: `InstructionInfo` trait for CFG construction
//! - [`graph`]: CFG data structures (`Cfg`, `BlockData`)
//! - [`builder`]: Generic CFG builder

pub mod arm64;
pub mod builder;
pub mod graph;
pub mod traits;

// Re-export commonly used types
pub use arm64::{CheckResult, ClassifiedOpcode, RejectionReason, BY_MNEMONIC};
pub use builder::build_cfg;
pub use graph::{BlockData, Cfg};
pub use traits::InstructionInfo;

// Re-export petgraph's NodeIndex for convenience
pub use petgraph::graph::NodeIndex;
