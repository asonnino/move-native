//! Control Flow Graph analysis for Arm64
//!
//! This crate provides:
//! - **CFG construction** from instruction sequences (text or binary)
//! - **Back-edge detection** using dominator analysis
//! - **Arm64 opcode classification** for control flow and verification
//!
//! # Architecture
//!
//! The crate provides two levels of abstraction via traits:
//!
//! - [`BasicInstruction`]: Minimal interface for mnemonic-based classification.
//!   Can be implemented by both resolved and unresolved instructions.
//!
//! - [`CfgInstruction`]: Full interface for CFG construction, extending
//!   `BasicInstruction` with target information. Implemented by:
//!   - Text assembly: `ResolvedInstruction` (instruction indices after label resolution)
//!   - Binary: `DecodedInstruction` (byte offsets)
//!
//! # Modules
//!
//! - [`arm64`]: Opcode classification and whitelist checking
//! - [`traits`]: `BasicInstruction` and `CfgInstruction` traits
//! - [`graph`]: CFG data structures (`Cfg`, `BlockData`)
//! - [`builder`]: Generic CFG builder

pub mod arm64;
pub mod builder;
pub mod graph;
pub mod traits;

pub use arm64::{BY_MNEMONIC, CheckResult, ClassifiedOpcode, RejectionReason};
pub use builder::build_cfg;
pub use graph::{BlockData, BlockIndex, Cfg};
pub use traits::{BasicInstruction, CfgInstruction};
