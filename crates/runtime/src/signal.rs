//! SIGTRAP handler for out-of-gas detection
//!
//! When the gas counter goes negative, the instrumented code executes `brk #0`
//! which triggers SIGTRAP. The signal handler advances PC past the trap
//! instruction so execution can cleanly unwind.
//!
//! Out-of-gas is detected by checking the gas counter (x23) after execution:
//! - `gas_remaining >= 0` → completed normally
//! - `gas_remaining < 0` → ran out of gas (trap was triggered)

use std::{mem::MaybeUninit, sync::OnceLock};

use crate::error::{RuntimeError, RuntimeResult};

// Once guard to ensure the handler is installed exactly once per process.
//
// This must be static (not a field of SignalHandler) because signal handler
// installation is a process-wide side effect - there's only one SIGTRAP handler
// per process, regardless of how many SignalHandler instances exist.
static HANDLER_INIT: OnceLock<RuntimeResult<()>> = OnceLock::new();

// Store our handler's address for verification.
// This allows us to detect if another component has replaced our handler.
static OUR_HANDLER: OnceLock<usize> = OnceLock::new();

/// Handle to the installed SIGTRAP signal handler
///
/// This is a zero-sized type. Creating a `SignalHandler` installs the SIGTRAP
/// handler if not already installed. Installation is idempotent - multiple
/// instances share the same underlying handler (which is process-wide).
///
/// The signal handler simply advances PC past the `brk #0` instruction.
/// Out-of-gas detection is done by checking if the gas counter (x23) is
/// negative after execution - no flag or TLS is needed.
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

    /// Query the current SIGTRAP handler
    fn query_current_handler() -> RuntimeResult<libc::sigaction> {
        unsafe {
            let mut sa = MaybeUninit::<libc::sigaction>::uninit();
            if libc::sigaction(libc::SIGTRAP, std::ptr::null(), sa.as_mut_ptr()) != 0 {
                return Err(RuntimeError::SignalSetupError {
                    reason: "failed to query signal handler".into(),
                });
            }
            Ok(sa.assume_init())
        }
    }

    /// Verify our handler is still installed
    ///
    /// This checks that the current SIGTRAP handler matches the one we installed.
    /// If another component has replaced our handler, gas metering will silently
    /// break (infinite loops instead of out-of-gas errors).
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The signal handler query fails
    /// - The handler was replaced by another component
    pub fn verify_installed(&self) -> RuntimeResult<()> {
        let current = Self::query_current_handler()?;

        let our_handler =
            OUR_HANDLER
                .get()
                .copied()
                .ok_or_else(|| RuntimeError::SignalSetupError {
                    reason: "handler address not recorded (install not called?)".into(),
                })?;
        if current.sa_sigaction != our_handler {
            return Err(RuntimeError::SignalSetupError {
                reason: "SIGTRAP handler was replaced by another component".into(),
            });
        }
        Ok(())
    }

    /// Inner implementation that performs the actual sigaction syscall
    fn install_inner() -> RuntimeResult<()> {
        // Check if a handler is already installed
        let old_sa = Self::query_current_handler()?;
        let handler_addr = old_sa.sa_sigaction;
        if handler_addr != 0 && handler_addr != libc::SIG_DFL && handler_addr != libc::SIG_IGN {
            return Err(RuntimeError::SignalSetupError {
                reason: "SIGTRAP handler already installed by another component".into(),
            });
        }

        // Safety: We're setting up a signal handler with valid parameters
        unsafe {
            // Zero-initialize the sigaction struct
            let mut sa: libc::sigaction = std::mem::zeroed();

            // Set our handler function (cast to pointer then usize for the union field)
            sa.sa_sigaction = Self::handle_sigtrap as *const () as usize;

            // SA_SIGINFO: use sa_sigaction (3-arg handler) instead of sa_handler (1-arg).
            // This gives us access to siginfo_t and ucontext_t, which we need to advance PC.
            // SA_RESTART: restart interrupted syscalls instead of returning EINTR.
            sa.sa_flags = libc::SA_SIGINFO | libc::SA_RESTART;

            // Initialize signal mask to empty (no signals blocked during handler)
            libc::sigemptyset(&mut sa.sa_mask);

            // Store our handler address for later verification
            OUR_HANDLER.get_or_init(|| Self::handle_sigtrap as *const () as usize);

            // Register the handler for SIGTRAP (raised by `brk #0`).
            // Args: signal number, new action, old action (null = don't save previous)
            if libc::sigaction(libc::SIGTRAP, &sa, std::ptr::null_mut()) != 0 {
                return Err(RuntimeError::SignalSetupError {
                    reason: format!("sigaction failed: {}", std::io::Error::last_os_error()),
                });
            }
        }
        Ok(())
    }

    /// Signal handler for SIGTRAP
    ///
    /// Advances PC past the `brk #0` instruction so execution can continue.
    /// Only handles brk traps - ignores debugger breakpoints and other
    /// SIGTRAP sources.
    ///
    /// Note: `#[inline(never)]` ensures this function has a stable address
    /// that can be compared in `verify_installed()`.
    #[inline(never)]
    extern "C" fn handle_sigtrap(
        _sig: libc::c_int,
        info: *mut libc::siginfo_t,
        ctx: *mut libc::c_void,
    ) {
        // Safety: info and ctx point to valid kernel-provided structures
        unsafe {
            Self::handle_brk_trap(info, ctx);
        }
    }

    /// Handle brk trap by advancing PC (macOS aarch64)
    ///
    /// Only advances PC for brk traps (si_code == 0 on macOS).
    /// ARM64 uses fixed-width 4-byte instructions, so `+= 4` always advances
    /// exactly one instruction.
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
    unsafe fn handle_brk_trap(info: *mut libc::siginfo_t, ctx: *mut libc::c_void) {
        // macOS: brk instruction generates si_code == 0
        // (Mach exceptions converted to POSIX signals lose detail)
        if (*info).si_code != 0 {
            return;
        }
        // macOS arm64 mcontext layout - PC is at a specific offset
        // The ucontext_t contains uc_mcontext which points to __darwin_mcontext64
        let uctx = ctx as *mut libc::ucontext_t;
        let mctx = (*uctx).uc_mcontext as *mut u8;
        // PC offset: 16 (__es) + 232 (__x[29]) + 24 (fp+lr+sp) = 272
        let pc_ptr = mctx.add(272) as *mut u64;
        *pc_ptr = (*pc_ptr).wrapping_add(4);
    }

    /// Handle brk trap by advancing PC (Linux aarch64)
    ///
    /// Only advances PC for brk traps (si_code == TRAP_BRKPT on Linux).
    /// ARM64 uses fixed-width 4-byte instructions, so `+= 4` always advances
    /// exactly one instruction.
    #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
    unsafe fn handle_brk_trap(info: *mut libc::siginfo_t, ctx: *mut libc::c_void) {
        // Linux: brk instruction generates si_code == TRAP_BRKPT (1)
        const TRAP_BRKPT: libc::c_int = 1;
        if (*info).si_code != TRAP_BRKPT {
            return;
        }
        let uctx = ctx as *mut libc::ucontext_t;
        (*uctx).uc_mcontext.pc += 4;
    }

    /// Fallback for unsupported platforms (compile-time error prevention)
    #[cfg(not(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))))]
    unsafe fn handle_brk_trap(_info: *mut libc::siginfo_t, _ctx: *mut libc::c_void) {
        panic!("unsupported platform for signal handler");
    }
}

#[cfg(test)]
mod tests {
    use crate::{error::RuntimeError, signal::SignalHandler};
    use serial_test::{parallel, serial};

    #[test]
    #[parallel(signal_handler)]
    fn test_install_handler() {
        // Installing the handler should succeed
        let _handler = SignalHandler::install().expect("failed to install handler");
        // Installing again should also succeed (idempotent)
        let _handler2 = SignalHandler::install().expect("failed to install handler second time");
    }

    #[test]
    #[parallel(signal_handler)]
    fn test_verify_installed_succeeds_after_install() {
        let handler = SignalHandler::install().expect("failed to install handler");
        // Verification should succeed immediately after install
        handler
            .verify_installed()
            .expect("verify_installed failed after install");
    }

    #[test]
    #[parallel(signal_handler)]
    fn test_verify_installed_succeeds_on_cloned_handler() {
        let handler = SignalHandler::install().expect("failed to install handler");
        let cloned = handler.clone();
        // Verification should work on cloned handlers too
        cloned
            .verify_installed()
            .expect("verify_installed failed on cloned handler");
    }

    #[test]
    #[parallel(signal_handler)]
    fn test_handler_address_is_recorded() {
        // After install, OUR_HANDLER should be set
        let _handler = SignalHandler::install().expect("failed to install handler");
        let recorded = super::OUR_HANDLER.get();
        assert!(
            recorded.is_some(),
            "OUR_HANDLER should be set after install"
        );
        assert_ne!(*recorded.unwrap(), 0, "handler address should not be zero");
    }

    // This test temporarily replaces the signal handler, which would cause other
    // tests to fail if they run concurrently. Must run serially within the group.
    #[test]
    #[serial(signal_handler)]
    fn test_verify_detects_handler_replacement() {
        let handler = SignalHandler::install().expect("failed to install handler");

        // Replace our handler with a dummy one
        extern "C" fn dummy_handler(_: libc::c_int, _: *mut libc::siginfo_t, _: *mut libc::c_void) {
            // Do nothing
        }

        unsafe {
            let mut sa: libc::sigaction = std::mem::zeroed();
            sa.sa_sigaction = dummy_handler as *const () as usize;
            sa.sa_flags = libc::SA_SIGINFO;
            libc::sigemptyset(&mut sa.sa_mask);

            // Save old handler so we can restore it
            let mut old_sa: libc::sigaction = std::mem::zeroed();
            assert_eq!(
                libc::sigaction(libc::SIGTRAP, &sa, &mut old_sa),
                0,
                "failed to replace handler"
            );

            // verify_installed should now fail
            let result = handler.verify_installed();
            assert!(
                result.is_err(),
                "verify_installed should fail after handler replacement"
            );

            if let Err(RuntimeError::SignalSetupError { reason }) = result {
                assert!(
                    reason.contains("replaced"),
                    "error should mention replacement: {reason}"
                );
            } else {
                panic!("unexpected error type");
            }

            // Restore our handler for other tests
            assert_eq!(
                libc::sigaction(libc::SIGTRAP, &old_sa, std::ptr::null_mut()),
                0,
                "failed to restore handler"
            );
        }

        // Verification should succeed again after restoration
        handler
            .verify_installed()
            .expect("verify_installed should succeed after restoration");
    }
}
