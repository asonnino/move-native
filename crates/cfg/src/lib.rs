//! Control Flow Graph analysis for Arm64

pub mod arm64;
pub mod block_graph;
pub mod builder;
pub mod call_graph;
pub mod traits;

pub use arm64::{BY_MNEMONIC, CheckResult, ClassifiedOpcode, RejectionReason};
pub use block_graph::{BlockData, BlockGraph, BlockIndex};
pub use builder::{CfgBuilder, build_block_graph};
pub use call_graph::build_call_graph;
pub use traits::{BasicInstruction, CfgInstruction};
