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
//! | **Instruction whitelist** | Base + SIMD + crypto allowed; reject atomics, FP, syscalls, barriers, PAC, MTE |
//! | **Gas check at back-edges** | Verify `sub x23` / `tbz x23, #63` / `brk #0` sequence before each back-edge |
//! | **x23 protection** | Gas counter only modified by gas decrement sequences |
//! | **No indirect branches** | Reject `br`, `blr`, `bra*`, `blra*` (`ret` is allowed — see below) |
//! | **No recursive calls** | Reject cyclic call graphs (mutual recursion via `bl` or tail calls) |
//! | **No unreachable code** | All basic blocks must be reachable from entry point (multi-root for multi-function code) |
//! | **Branch targets valid** | All branch targets must be valid instruction boundaries |
//! | **SP safety** | Only recognized SP modification patterns allowed (no dynamic stack allocation) |
//! | **Stack depth** | Worst-case stack depth must be within budget (bounded by gas budget for loops) |
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
