// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Native verifier for Arm64 binaries
//!
//! Verifies that compiled code is safe for deterministic execution by checking
//! a series of properties on the machine code. Based on the DeCl paper
//! (OSDI 2025 - "Deterministic Client: Enforcing Determinism on Untrusted Machine Code").
//!
//! # Verification Checklist
//!
//! | Check | Description |
//! |-------|-------------|
//! | **Instruction whitelist** | Reject atomics, FP, syscalls, barriers, PAC, MTE |
//! | **Gas check at back-edges** | `sub x23`/`tbz x23,#63`/`brk #0` before back-edges |
//! | **x23 protection** | Gas counter only modified by gas decrements |
//! | **No indirect branches** | Reject `br`, `blr`, `bra*`, `blra*` (`ret` ok) |
//! | **No recursive calls** | Reject cyclic call graphs (via `bl` or tail calls) |
//! | **No unreachable code** | All blocks reachable from entry point |
//! | **Branch targets valid** | All targets must be instruction boundaries |
//! | **SP safety** | Only recognized SP patterns (no dynamic alloc) |
//! | **Stack depth** | Worst-case depth within budget (bounded by gas) |
//!
//! TODO: Not yet implemented:
//! - Malformed encodings: reject UNPREDICTABLE (bad SBZ/SBO fields) and unallocated encodings
//! - UNPREDICTABLE patterns: reject patterns like `ldr x0, [x0], #16` (writeback to same register)

mod decode;
mod error;
mod gas;
mod stack;
mod verify;

pub use cfg::{CheckResult, RejectionReason};
pub use decode::{DecodedInstruction, decode_instructions};
pub use error::{DecodeError, VerificationError, VerificationResult};
pub use gas::{DEFAULT_GAS_BUDGET, GasEffect};
pub use stack::DEFAULT_STACK_BUDGET;
pub use verify::Verifier;
