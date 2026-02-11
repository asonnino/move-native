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
//! | **Malformed encodings** | Reject UNPREDICTABLE (bad SBZ/SBO fields) and unallocated encodings |
//! | **UNPREDICTABLE patterns** | Reject patterns like `ldr x0, [x0], #16` (writeback to same register) |
//! | **Gas check at back-edges** | Verify `sub x23` / `tbz x23, #63` / `brk #0` sequence before each back-edge |
//! | **x23 protection** | Gas counter only modified by gas decrement sequences |
//! | **No indirect branches** | Reject `br`, `blr`, `bra*`, `blra*` (`ret` is allowed — see below) |
//! | **No unreachable code** | All basic blocks must be reachable from entry point (multi-root for multi-function code) |
//! | **Branch targets valid** | All branch targets must be valid instruction boundaries |
//! | **SP safety** | Only recognized SP modification patterns allowed (no dynamic stack allocation) |
//! | **Stack depth** | Worst-case stack depth must be within budget (static analysis via call graph) |
//!
//! ## Why `ret` is allowed
//!
//! `ret` is safe because all reachable code is verified (whitelisted, gas-checked,
//! x23-protected). If `ret` lands in verified code, gas checks work. If it lands
//! outside the code section, SIGSEGV is caught by the fault handler. The DeCl paper
//! also allows `ret`.
//!
//! # Why Verify Machine Code?
//!
//! The verifier operates on the final binary (not assembly text) because:
//!
//! 1. **Trust boundary**: The CPU executes machine code, not assembly text
//! 2. **Assembler independence**: Don't trust the assembler to produce correct output
//! 3. **Production deployment**: Validators receive compiled binaries, not source
//!
//! The gas-instrument tool is "best effort" tooling; native-verifier provides
//! the security guarantee.
//!
//! # Gas Check Sequence
//!
//! At every back-edge (loop), the verifier expects this exact sequence:
//!
//! ```asm
//! sub x23, x23, #N      // decrement gas by N (instructions in block)
//! tbz x23, #63, .Lok    // if bit 63 is 0 (positive), continue
//! brk #0                // trap - out of gas
//! .Lok:
//! <back-edge branch>    // the original loop branch
//! ```
//!
//! # Unreachable Code
//!
//! Dead code is rejected because an unrelated bug could allow jumping into
//! uninstrumented dead code containing an infinite loop. All basic blocks
//! must be reachable from the entry point (or from function entries reachable
//! via the call graph).

mod decode;
mod error;
mod stack;
mod verify;

pub use cfg::{CheckResult, RejectionReason};
pub use decode::{DecodeError, DecodedInstruction, decode_instructions};
pub use error::{VerificationError, VerificationResult};
pub use stack::DEFAULT_STACK_BUDGET;
pub use verify::Verifier;
