//! Signal handlers for gas exhaustion and memory fault detection
//!
//! ## SIGTRAP (Out-of-Gas)
//!
//! When the gas counter goes negative, the instrumented code executes `brk #0`
//! which triggers SIGTRAP. The signal handler advances PC past the trap
//! instruction so execution can cleanly unwind.
//!
//! Out-of-gas is detected by checking the gas counter (x23) after execution:
//! - `gas_remaining >= 0` → completed normally
//! - `gas_remaining < 0` → ran out of gas (trap was triggered)
//!
//! ## SIGSEGV/SIGBUS (Memory Faults)
//!
//! Memory faults are handled by setting a TLS flag, restoring SP to a known-good
//! value, and redirecting PC to a saved return address in the executor's asm block.
//! This bypasses LR entirely, which is necessary because nested `bl` calls inside
//! Move code clobber LR. This follows the DeCl paper approach: "terminate programs
//! after a memory fault."
//!
//! # Warning: Debugger Interaction
//!
//! Do not attach a debugger with breakpoints during native code execution.
//! Breakpoints generate SIGTRAP signals that conflict with our gas exhaustion
//! handling. Our handler only advances PC for `brk` traps (si_code == 0 on macOS,
//! TRAP_BRKPT on Linux); for other SIGTRAP sources like debugger breakpoints,
//! we return without advancing PC, which causes the signal to be re-delivered
//! infinitely.

use std::{mem::MaybeUninit, sync::OnceLock};

use crate::{
    error::{RuntimeError, RuntimeResult},
    fault::{get_return_pc, get_saved_sp, is_in_move_execution, record_fault},
};

// Once guard to ensure the handler is installed exactly once per process.
//
// This must be static (not a field of SignalHandler) because signal handler
// installation is a process-wide side effect - there's only one SIGTRAP handler
// per process, regardless of how many SignalHandler instances exist.
static HANDLER_INIT: OnceLock<RuntimeResult<()>> = OnceLock::new();

// Store our handler addresses for verification.
// This allows us to detect if another component has replaced our handlers.
static OUR_TRAP_HANDLER: OnceLock<usize> = OnceLock::new();
static OUR_FAULT_HANDLER: OnceLock<usize> = OnceLock::new();

/// SA_SIGINFO-style signal handler signature.
type SigActionFn = extern "C" fn(libc::c_int, *mut libc::siginfo_t, *mut libc::c_void);

/// Signal table: (signal, handler_fn, addr_lock, reject_preexisting, name)
///
/// `reject_preexisting`: SIGTRAP has no fallback path — our handler blindly
/// advances PC, which is wrong for non-brk traps (e.g. debugger breakpoints).
/// SIGSEGV/SIGBUS handlers already reset to SIG_DFL for non-Move faults, so
/// pre-existing handlers (Rust runtime stack overflow, crash reporters) are
/// safely superseded.
const HANDLER_TABLE: [(libc::c_int, SigActionFn, &OnceLock<usize>, bool, &str); 3] = [
    (
        libc::SIGTRAP,
        SignalHandler::handle_sigtrap,
        &OUR_TRAP_HANDLER,
        true,
        "SIGTRAP",
    ),
    (
        libc::SIGSEGV,
        SignalHandler::handle_fault,
        &OUR_FAULT_HANDLER,
        false,
        "SIGSEGV",
    ),
    (
        libc::SIGBUS,
        SignalHandler::handle_fault,
        &OUR_FAULT_HANDLER,
        false,
        "SIGBUS",
    ),
];

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

    /// Query the current handler for a given signal
    ///
    /// # Safety
    ///
    /// Calls `libc::sigaction` — must only be called with a valid signal number.
    unsafe fn query_handler(signal: libc::c_int) -> RuntimeResult<libc::sigaction> {
        let mut sa = MaybeUninit::<libc::sigaction>::uninit();
        if libc::sigaction(signal, std::ptr::null(), sa.as_mut_ptr()) != 0 {
            return Err(RuntimeError::SignalSetupError {
                reason: format!("failed to query signal handler for signal {}", signal),
            });
        }
        Ok(sa.assume_init())
    }

    /// Verify our handlers are still installed
    ///
    /// This checks that the current SIGTRAP, SIGSEGV, and SIGBUS handlers
    /// match the ones we installed. If another component has replaced any
    /// handler, gas metering or fault recovery will silently break.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - A signal handler query fails
    /// - Any handler was replaced by another component
    pub fn verify_installed(&self) -> RuntimeResult<()> {
        for (signal, _, expected_lock, _, name) in HANDLER_TABLE {
            let current = unsafe { Self::query_handler(signal)? };
            let expected =
                expected_lock
                    .get()
                    .copied()
                    .ok_or_else(|| RuntimeError::SignalSetupError {
                        reason: format!(
                            "{} handler address not recorded (install not called?)",
                            name
                        ),
                    })?;
            if current.sa_sigaction != expected {
                return Err(RuntimeError::SignalSetupError {
                    reason: format!("{} handler was replaced by another component", name),
                });
            }
        }
        Ok(())
    }

    /// Inner implementation that performs the actual sigaction syscalls
    fn install_inner() -> RuntimeResult<()> {
        for (signal, handler_fn, addr_lock, reject_preexisting, name) in HANDLER_TABLE {
            let handler = handler_fn as usize;
            // Check for pre-existing handler (only reject when flagged)
            // Safety: signal numbers above are valid.
            if reject_preexisting {
                let old_sa = unsafe { Self::query_handler(signal)? };
                let old_addr = old_sa.sa_sigaction;
                if old_addr != 0 && old_addr != libc::SIG_DFL && old_addr != libc::SIG_IGN {
                    return Err(RuntimeError::SignalSetupError {
                        reason: format!("{} handler already installed by another component", name),
                    });
                }
            }

            // Record our handler address for verify_installed()
            addr_lock.get_or_init(|| handler);

            // Install our handler
            // Safety: We're setting up signal handlers with valid parameters.
            // SA_SIGINFO: use sa_sigaction (3-arg handler) instead of sa_handler (1-arg).
            // This gives us access to siginfo_t and ucontext_t, which we need to advance PC.
            // SA_RESTART: restart interrupted syscalls instead of returning EINTR.
            unsafe {
                let mut sa: libc::sigaction = std::mem::zeroed();
                sa.sa_sigaction = handler;
                sa.sa_flags = libc::SA_SIGINFO | libc::SA_RESTART;
                libc::sigemptyset(&mut sa.sa_mask);
                if libc::sigaction(signal, &sa, std::ptr::null_mut()) != 0 {
                    return Err(RuntimeError::SignalSetupError {
                        reason: format!(
                            "{} sigaction failed: {}",
                            name,
                            std::io::Error::last_os_error()
                        ),
                    });
                }
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

    /// Signal handler for memory faults (SIGSEGV/SIGBUS)
    ///
    /// Only handles faults that occur during Move native code execution.
    /// If the fault originated outside Move execution (e.g., a Rust bug on a
    /// networking thread), resets to SIG_DFL so the kernel re-delivers the
    /// signal with default disposition — producing a clean crash with core dump.
    ///
    /// Note: `#[inline(never)]` ensures this function has a stable address.
    #[inline(never)]
    extern "C" fn handle_fault(
        sig: libc::c_int,
        _info: *mut libc::siginfo_t,
        ctx: *mut libc::c_void,
    ) {
        // Guard: only handle faults from Move execution.
        // MOVE_EXECUTION_DEPTH is non-zero only while execute_with_gas is running.
        if !is_in_move_execution() {
            // Not in Move execution — restore default handler so the kernel
            // re-delivers the signal, producing a clean crash with core dump.
            // sigaction() is async-signal-safe per POSIX.
            unsafe {
                let mut sa: libc::sigaction = std::mem::zeroed();
                sa.sa_sigaction = libc::SIG_DFL;
                libc::sigemptyset(&mut sa.sa_mask);
                libc::sigaction(sig, &sa, std::ptr::null_mut());
            }
            return;
        }

        // Record fault (thread-local write, no synchronization needed)
        record_fault();

        // Restore SP and redirect PC
        unsafe {
            Self::restore_sp_and_redirect_pc(ctx);
        }
    }

    /// Restore SP and redirect PC to saved return address (macOS aarch64)
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    unsafe fn restore_sp_and_redirect_pc(ctx: *mut libc::c_void) {
        let saved_sp = get_saved_sp();
        let return_pc = get_return_pc();

        let uctx = ctx as *mut libc::ucontext_t;
        let mctx = (*uctx).uc_mcontext as *mut u8;

        // SP offset: 16 (__es) + 232 (__x[29]) + 8 (fp) + 8 (lr) = 264
        let sp_ptr = mctx.add(264) as *mut u64;
        *sp_ptr = saved_sp;

        // PC offset: 272
        let pc_ptr = mctx.add(272) as *mut u64;
        *pc_ptr = return_pc;
    }

    /// Restore SP and redirect PC to saved return address (Linux aarch64)
    #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
    unsafe fn restore_sp_and_redirect_pc(ctx: *mut libc::c_void) {
        let saved_sp = get_saved_sp();
        let return_pc = get_return_pc();

        let uctx = ctx as *mut libc::ucontext_t;
        (*uctx).uc_mcontext.sp = saved_sp;
        (*uctx).uc_mcontext.pc = return_pc;
    }

    /// Fallback for unsupported platforms
    #[cfg(not(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))))]
    unsafe fn restore_sp_and_redirect_pc(_ctx: *mut libc::c_void) {
        panic!("unsupported platform for fault handler");
    }
}

#[cfg(test)]
mod tests {
    use serial_test::{parallel, serial};

    use crate::{error::RuntimeError, signal::SignalHandler};

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
    fn test_handler_addresses_are_recorded() {
        // After install, both handler addresses should be set
        let _handler = SignalHandler::install().expect("failed to install handler");

        let trap = super::OUR_TRAP_HANDLER.get();
        assert!(
            trap.is_some(),
            "OUR_TRAP_HANDLER should be set after install"
        );
        assert_ne!(*trap.unwrap(), 0, "trap handler address should not be zero");

        let fault = super::OUR_FAULT_HANDLER.get();
        assert!(
            fault.is_some(),
            "OUR_FAULT_HANDLER should be set after install"
        );
        assert_ne!(
            *fault.unwrap(),
            0,
            "fault handler address should not be zero"
        );
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
