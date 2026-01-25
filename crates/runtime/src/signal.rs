//! SIGTRAP handler for out-of-gas detection
//!
//! When the gas counter goes negative, the instrumented code executes `brk #0`
//! which triggers SIGTRAP. The signal handler sets a flag and advances PC past
//! the trap instruction so execution can cleanly unwind.

use std::{cell::Cell, sync::OnceLock};

use libc::{c_int, c_void, sigaction, siginfo_t, SA_SIGINFO, SIGTRAP};

use crate::error::{RuntimeError, RuntimeResult};

// Once guard to ensure the handler is installed exactly once per process.
//
// This must be static (not a field of SignalHandler) because signal handler
// installation is a process-wide side effect - there's only one SIGTRAP handler
// per process, regardless of how many SignalHandler instances exist.
static HANDLER_INIT: OnceLock<RuntimeResult<()>> = OnceLock::new();

// Thread-local flag indicating out-of-gas condition.
//
// This must be static (not a field of SignalHandler) because the signal handler
// callback (`handle_sigtrap`) is invoked by the kernel with a fixed signature
// and cannot access instance data - only global/thread-local state.
//
// It's thread-local (not global) because:
// 1. Each thread has its own x23 register (gas counter)
// 2. SIGTRAP from `brk #0` is a synchronous signal, delivered to the thread
//    that executed the instruction
// 3. This allows parallel execution of gas-instrumented code across threads
thread_local! {
    static OUT_OF_GAS: Cell<bool> = const { Cell::new(false) };
}

/// Handle to the installed SIGTRAP signal handler
///
/// This is a zero-sized type that provides methods for checking and resetting
/// the out-of-gas flag. The out-of-gas flag is thread-local, allowing parallel
/// execution of gas-instrumented code across threads.
///
/// Creating a `SignalHandler` installs the SIGTRAP handler if not already
/// installed. Installation is idempotent - multiple instances share the same
/// underlying handler (which is process-wide), but each thread has its own
/// out-of-gas flag.
#[derive(Clone)]
pub(crate) struct SignalHandler;

impl SignalHandler {
    /// Install the SIGTRAP handler and return a handle
    ///
    /// Uses `OnceLock` to ensure the handler is installed exactly once per
    /// process. After the first call, subsequent calls are nearly free
    /// (just an atomic check).
    ///
    /// # Errors
    ///
    /// Returns an error if the signal handler cannot be installed.
    pub fn install() -> RuntimeResult<Self> {
        HANDLER_INIT.get_or_init(Self::install_inner).clone()?;
        Ok(Self)
    }

    /// Check if the last execution ran out of gas
    pub fn is_out_of_gas(&self) -> bool {
        OUT_OF_GAS.with(|flag| flag.get())
    }

    /// Reset the out-of-gas flag before execution
    pub fn reset(&self) {
        OUT_OF_GAS.with(|flag| flag.set(false));
    }

    /// Inner implementation that performs the actual sigaction syscall
    fn install_inner() -> RuntimeResult<()> {
        // Safety: We're setting up a signal handler with valid parameters
        unsafe {
            // Zero-initialize the sigaction struct
            let mut sa: sigaction = std::mem::zeroed();

            // Set our handler function (cast to usize for the union field)
            sa.sa_sigaction = Self::handle_sigtrap as usize;

            // SA_SIGINFO: use sa_sigaction (3-arg handler) instead of sa_handler (1-arg).
            // This gives us access to siginfo_t and ucontext_t, which we need to advance PC.
            sa.sa_flags = SA_SIGINFO;

            // Register the handler for SIGTRAP (raised by `brk #0`).
            // Args: signal number, new action, old action (null = don't save previous)
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
    /// Sets the thread-local OUT_OF_GAS flag and advances PC past the brk instruction.
    /// Since SIGTRAP is a synchronous signal, it runs on the same thread that
    /// executed `brk #0`, so accessing thread-local storage is safe.
    extern "C" fn handle_sigtrap(_sig: c_int, _info: *mut siginfo_t, ctx: *mut c_void) {
        OUT_OF_GAS.with(|flag| flag.set(true));
        // Safety: ctx points to a valid ucontext_t from the kernel
        unsafe {
            Self::advance_pc(ctx);
        }
    }

    /// Advance PC past the brk instruction (macOS aarch64)
    ///
    /// FRAGILE: This uses a hardcoded offset (272) into the mcontext struct because
    /// the `libc` crate doesn't expose mcontext fields on macOS. If Apple changes
    /// the struct layout in a future macOS version, this will silently break.
    /// This is acceptable because macOS is only used for local development - the
    /// production target is Linux, which uses proper struct access via `libc`.
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
    #[cfg(not(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))))]
    unsafe fn advance_pc(_ctx: *mut c_void) {
        // This will be unreachable on supported platforms
        // On unsupported platforms, this prevents compilation errors
        // but execution will fail at runtime
        panic!("unsupported platform for signal handler");
    }
}

#[cfg(test)]
mod tests {
    use crate::signal::{SignalHandler, OUT_OF_GAS};

    #[test]
    fn test_out_of_gas_flag() {
        let handler = SignalHandler::install().expect("failed to install handler");
        handler.reset();
        assert!(!handler.is_out_of_gas());

        OUT_OF_GAS.with(|flag| flag.set(true));
        assert!(handler.is_out_of_gas());

        handler.reset();
        assert!(!handler.is_out_of_gas());
    }

    #[test]
    fn test_install_handler() {
        // Installing the handler should succeed
        let _handler = SignalHandler::install().expect("failed to install handler");
        // Installing again should also succeed (idempotent)
        let _handler2 = SignalHandler::install().expect("failed to install handler second time");
    }
}
