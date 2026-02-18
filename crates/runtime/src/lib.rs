#![feature(thread_local)]
// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Execution runtime for gas-instrumented native Move code
//!
//! This crate provides the runtime environment for executing Arm64 code
//! that has been instrumented with gas metering. Based on the DeCl paper
//! (OSDI 2025 - "Deterministic Client: Enforcing Determinism on Untrusted Machine Code").
//!
//! # Overview
//!
//! The runtime handles:
//! - Loading native modules into pre-allocated executable memory slots
//! - Setting up the gas counter in register x23
//! - Installing a SIGTRAP handler to catch out-of-gas conditions
//! - Executing functions and reporting gas consumption
//!
//! # Architecture
//!
//! ```text
//! ModuleStore (persistent storage)
//!      ↓ fetch on cache miss
//! ModuleCache (LRU, backed by Pool/Slots)
//!      ↓
//! FunctionHandle → Executor
//! ```
//!
//! # Gas Instrumentation Protocol
//!
//! The runtime expects code instrumented with the following sequence at back-edges:
//!
//! ```asm
//! sub x23, x23, #N      // decrement gas by N (instructions in block)
//! tbz x23, #63, .Look    // if bit 63 is 0 (positive), continue
//! brk #0                // trap - out of gas
//! .Look:
//! <back-edge branch>    // the original loop branch
//! ```
//!
//! When gas goes negative and `brk #0` is executed, the SIGTRAP handler:
//! 1. Sets an out-of-gas flag
//! 2. Advances PC past the brk instruction
//! 3. Allows execution to cleanly return
//!
//! # Platform Support
//!
//! Currently supported platforms:
//! - macOS on Apple Silicon (aarch64-apple-darwin)
//! - Linux on aarch64 (aarch64-unknown-linux-gnu)
//!
//! # Thread Safety
//!
//! The runtime supports parallel execution of gas-instrumented code across threads.
//! Each thread has its own out-of-gas flag (thread-local storage), and since SIGTRAP
//! is a synchronous signal delivered to the thread that executed `brk #0`, there is
//! no cross-talk between concurrent executions.

mod cache;
mod error;
mod execute;
mod fault;
mod module;
mod signal;
mod slot;
mod store;

pub use cache::ModuleCache;
pub use error::{RuntimeError, RuntimeResult};
pub use execute::{ExecutionStatus, Executor, GasResult, MAX_GAS_LIMIT};
pub use module::{CompiledModule, FunctionHandle};
pub use slot::SlotPool;
#[cfg(test)]
pub use store::mock::MockStore;
pub use store::{MemoryStore, ModuleStore};
