//! Execution runtime for gas-instrumented native Move code
//!
//! This crate provides the runtime environment for executing Arm64 code
//! that has been instrumented with gas metering. Based on the DeCl paper
//! (OSDI 2025 - "Deterministic Client: Enforcing Determinism on Untrusted Machine Code").
//!
//! # Overview
//!
//! The runtime handles:
//! - Loading native modules (.dylib on macOS, .so on Linux)
//! - Setting up the gas counter in register x23
//! - Installing a SIGTRAP handler to catch out-of-gas conditions
//! - Executing functions and reporting gas consumption
//!
//! # Gas Instrumentation Protocol
//!
//! The runtime expects code instrumented with the following sequence at back-edges:
//!
//! ```asm
//! sub x23, x23, #N      // decrement gas by N (instructions in block)
//! tbz x23, #63, .Lok    // if bit 63 is 0 (positive), continue
//! brk #0                // trap - out of gas
//! .Lok:
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
mod loader;
mod signal;

pub use cache::{ModuleCache, ModuleId};
pub use error::{RuntimeError, RuntimeResult};
pub use execute::{Executor, GasResult};
pub use loader::{NativeModule, Symbol};
