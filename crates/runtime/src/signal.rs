//! SIGTRAP handler for out-of-gas detection
//!
//! When the gas counter goes negative, the instrumented code executes `brk #0`
//! which triggers SIGTRAP. The signal handler sets a flag and advances PC past
//! the trap instruction so execution can cleanly unwind.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::OnceLock;

use libc::{c_int, c_void, sigaction, siginfo_t, SA_SIGINFO, SIGTRAP};

use crate::error::{RuntimeError, RuntimeResult};

/// Once guard to ensure the handler is installed exactly once per process,
/// storing the cached result from installation.
static HANDLER_INIT: OnceLock<RuntimeResult<()>> = OnceLock::new();

/// Global flag indicating out-of-gas condition
static OUT_OF_GAS: AtomicBool = AtomicBool::new(false);

/// Check if the last execution ran out of gas
pub fn is_out_of_gas() -> bool {
    OUT_OF_GAS.load(Ordering::SeqCst)
}

/// Reset the out-of-gas flag before execution
pub fn reset_out_of_gas() {
    OUT_OF_GAS.store(false, Ordering::SeqCst);
}

/// Install the SIGTRAP handler (once per process)
///
/// Uses `OnceLock` to ensure the handler is installed exactly once, regardless
/// of how many times this function is called. After the first call, subsequent
/// calls are nearly free (just an atomic check).
///
/// # Safety
/// This modifies global process state (signal handlers).
/// Must be called before executing any gas-instrumented code.
pub fn install_handler() -> RuntimeResult<()> {
    HANDLER_INIT.get_or_init(install_handler_inner).clone()
}

/// Inner implementation that performs the actual sigaction syscall
fn install_handler_inner() -> RuntimeResult<()> {
    unsafe {
        let mut sa: sigaction = std::mem::zeroed();
        sa.sa_sigaction = sigtrap_handler as usize;
        sa.sa_flags = SA_SIGINFO;

        if sigaction(SIGTRAP, &sa, std::ptr::null_mut()) != 0 {
            return Err(RuntimeError::SignalSetupError {
                reason: format!("sigaction failed: {}", std::io::Error::last_os_error()),
            });
        }
    }
    Ok(())
}

/// Signal handler for SIGTRAP
///
/// Sets the OUT_OF_GAS flag and advances PC past the brk instruction.
extern "C" fn sigtrap_handler(_sig: c_int, _info: *mut siginfo_t, ctx: *mut c_void) {
    OUT_OF_GAS.store(true, Ordering::SeqCst);
    // Safety: ctx points to a valid ucontext_t from the kernel
    unsafe {
        advance_pc(ctx);
    }
}

/// Advance PC past the brk instruction (macOS aarch64)
///
/// On macOS, the mcontext structure layout is:
/// - __es: exception state (16 bytes)
/// - __x[29]: general registers x0-x28 (29 * 8 = 232 bytes)
/// - __fp, __lr, __sp: frame pointer, link register, stack pointer (24 bytes)
/// - __pc: program counter at offset 272
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
unsafe fn advance_pc(ctx: *mut c_void) {
    // macOS arm64 mcontext layout - PC is at a specific offset
    // The ucontext_t contains uc_mcontext which points to __darwin_mcontext64
    let uctx = ctx as *mut libc::ucontext_t;
    let mctx = (*uctx).uc_mcontext as *mut u8;
    // PC offset: 16 (__es) + 232 (__x[29]) + 24 (fp+lr+sp) = 272
    let pc_ptr = mctx.add(272) as *mut u64;
    *pc_ptr = (*pc_ptr).wrapping_add(4);
}

/// Advance PC past the brk instruction (Linux aarch64)
///
/// On Linux, the ucontext_t provides direct access to the mcontext
/// which contains the PC register.
#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
unsafe fn advance_pc(ctx: *mut c_void) {
    let uctx = ctx as *mut libc::ucontext_t;
    (*uctx).uc_mcontext.pc += 4;
}

/// Fallback for unsupported platforms (compile-time error prevention)
#[cfg(not(all(
    target_arch = "aarch64",
    any(target_os = "macos", target_os = "linux")
)))]
unsafe fn advance_pc(_ctx: *mut c_void) {
    // This will be unreachable on supported platforms
    // On unsupported platforms, this prevents compilation errors
    // but execution will fail at runtime
    panic!("unsupported platform for signal handler");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_out_of_gas_flag() {
        reset_out_of_gas();
        assert!(!is_out_of_gas());

        OUT_OF_GAS.store(true, Ordering::SeqCst);
        assert!(is_out_of_gas());

        reset_out_of_gas();
        assert!(!is_out_of_gas());
    }

    #[test]
    fn test_install_handler() {
        // Installing the handler should succeed
        install_handler().expect("failed to install handler");
        // Installing again should also succeed (idempotent)
        install_handler().expect("failed to install handler second time");
    }
}
