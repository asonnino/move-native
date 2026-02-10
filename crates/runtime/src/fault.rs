//! Fault handling for memory faults (SIGSEGV/SIGBUS)
//!
//! This module provides state for handling memory faults during native code
//! execution. Following the DeCl paper approach: "terminate programs after
//! a memory fault."
//!
//! # Design
//!
//! When a memory fault occurs:
//! 1. Signal handler sets a flag and restores SP to a known-good value
//! 2. PC is redirected to the saved return address (bypassing LR entirely)
//! 3. Execution resumes at the instruction after `blr {entry}` in the asm block
//! 4. The executor checks the flag
//!
//! # Thread Safety
//!
//! Uses `#[thread_local]` statics so each thread has isolated fault state.
//! This is safe because SIGSEGV/SIGBUS are synchronous signals delivered
//! to the faulting thread, so there is no cross-thread access to the same
//! TLS instance. `Cell` is appropriate here because signal handlers run on
//! the same thread (no concurrent access to the same TLS instance).

use std::cell::Cell;

/// Guard flag: true only while executing Move native code via `execute_with_gas`.
/// The SIGSEGV/SIGBUS handler checks this to distinguish Move faults from
/// unrelated faults on the same thread.
#[thread_local]
static IN_MOVE_EXECUTION: Cell<bool> = Cell::new(false);

/// Flag indicating a memory fault occurred (SIGSEGV/SIGBUS)
/// Thread-local so each thread has isolated fault state.
#[thread_local]
static FAULT_OCCURRED: Cell<bool> = Cell::new(false);

/// Saved stack pointer - set inside asm block, read by signal handler
/// Thread-local so each thread has isolated fault state.
#[thread_local]
static SAVED_SP: Cell<u64> = Cell::new(0);

/// Record that a fault occurred (called from signal handler)
#[inline]
pub fn record_fault() {
    FAULT_OCCURRED.set(true);
}

/// Check if a fault occurred (called after execution)
/// Returns true if fault occurred, and clears the flag
#[inline]
pub fn take_fault() -> bool {
    let occurred = FAULT_OCCURRED.get();
    if occurred {
        FAULT_OCCURRED.set(false);
    }
    occurred
}

/// Get pointer to SAVED_SP for use in inline asm
/// The asm block will store SP to this address after its own stack push
#[inline]
pub fn saved_sp_ptr() -> *mut u64 {
    SAVED_SP.as_ptr() as *mut u64
}

/// Get the saved stack pointer (called from signal handler)
#[inline]
pub fn get_saved_sp() -> u64 {
    SAVED_SP.get()
}

/// Mark that we are entering Move native code execution
#[inline]
pub fn set_in_move_execution(active: bool) {
    IN_MOVE_EXECUTION.set(active);
}

/// Check whether the current thread is executing Move native code
#[inline]
pub fn is_in_move_execution() -> bool {
    IN_MOVE_EXECUTION.get()
}

/// Saved return PC — the address right after `blr {entry}` in the asm block.
/// The signal handler redirects PC here on fault, bypassing LR entirely.
/// This is necessary because nested `bl` calls inside Move code clobber LR,
/// so we cannot rely on `ret` to return to the executor.
#[thread_local]
static RETURN_PC: Cell<u64> = Cell::new(0);

/// Get pointer to RETURN_PC for use in inline asm
/// The asm block will store the return address to this location before `blr {entry}`
#[inline]
pub fn saved_return_pc_ptr() -> *mut u64 {
    RETURN_PC.as_ptr() as *mut u64
}

/// Get the saved return PC (called from signal handler)
#[inline]
pub fn get_return_pc() -> u64 {
    RETURN_PC.get()
}

#[cfg(test)]
mod tests {
    use super::{
        get_return_pc,
        get_saved_sp,
        record_fault,
        saved_return_pc_ptr,
        saved_sp_ptr,
        take_fault,
    };

    #[test]
    fn test_take_fault_returns_false_when_not_set() {
        // Ensure flag is clear by taking any existing fault
        let _ = take_fault();
        assert!(!take_fault());
    }

    #[test]
    fn test_take_fault_returns_true_and_clears_when_set() {
        // Ensure flag is clear first
        let _ = take_fault();
        // Set the flag
        record_fault();
        // First take should return true
        assert!(take_fault());
        // Second take should return false (cleared)
        assert!(!take_fault());
    }

    #[test]
    fn test_saved_sp_operations() {
        let ptr = saved_sp_ptr();
        assert!(!ptr.is_null());
        // Write via pointer and read back
        unsafe {
            ptr.write(0x12345678);
        }
        assert_eq!(get_saved_sp(), 0x12345678);
    }

    #[test]
    fn test_return_pc_operations() {
        let ptr = saved_return_pc_ptr();
        assert!(!ptr.is_null());
        // Write via pointer and read back
        unsafe {
            ptr.write(0xDEADBEEF);
        }
        assert_eq!(get_return_pc(), 0xDEADBEEF);
    }
}
