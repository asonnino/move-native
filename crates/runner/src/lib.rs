// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Unified pipeline for Move native compilation
//!
//! Chains the full compilation pipeline into a single call:
//! Move bytecode -> LLVM assembly -> gas instrumentation -> assemble -> verify
//!
//! # Usage
//!
//! ```ignore
//! let module = runner::prepare(&bytecode)?;
//! // module is now a runtime::CompiledModule ready for execution
//! ```

pub mod assembler;
pub mod error;
pub mod pipeline;

pub use error::PipelineError;
pub use pipeline::{prepare, prepare_module};

// Re-export runtime types that consumers need for execution
pub use runtime::{
    CompiledModule, ExecutionStatus, Executor, GasResult, ModuleCache, ModuleStore, SlotPool,
};
