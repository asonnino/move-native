//! Executor for gas-instrumented native code
//!
//! The Executor handles signal handler installation and provides the
//! execution API for running gas-instrumented Arm64 code.
//!
//! # Warning: Debugger Interaction
//!
//! Do not attach a debugger with breakpoints during native code execution.
//! Breakpoints generate SIGTRAP signals that conflict with gas exhaustion
//! handling. See [`crate::signal`] module docs for details.

use std::arch::asm;

use crate::{
    error::{RuntimeError, RuntimeResult},
    fault::{saved_return_pc_ptr, saved_sp_ptr, set_in_move_execution, take_fault},
    module::FunctionHandle,
    signal::SignalHandler,
};

/// Maximum practical gas limit (10^15)
///
/// While the gas counter can technically hold up to i64::MAX, this limit
/// catches likely bugs (e.g., passing uninitialized or corrupted values).
/// 10^15 gas would allow ~11 days of computation at 1 instruction/ns.
pub const MAX_GAS_LIMIT: u64 = 1_000_000_000_000_000; // 10^15

/// Execution status after running native code
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecutionStatus {
    /// Execution completed normally
    Completed,
    /// Ran out of gas (trap was triggered)
    OutOfGas,
    /// Memory fault occurred (SIGSEGV or SIGBUS)
    Fault,
}

/// Result of executing native code
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GasResult {
    /// Execution status: completed, out-of-gas, or fault
    pub status: ExecutionStatus,
    /// Amount of gas consumed during execution
    pub gas_consumed: u64,
    /// Remaining gas after execution (clamped to 0 if exhausted)
    pub gas_remaining: u64,
}

impl GasResult {
    /// Returns true if execution completed normally (no out-of-gas or fault)
    ///
    /// Provided for backward compatibility and convenience.
    #[inline]
    pub fn completed(&self) -> bool {
        self.status == ExecutionStatus::Completed
    }
}

/// Executor for gas-instrumented native code
///
/// Handles signal handler installation and provides the execution API.
/// This is effectively zero-sized - it holds a `SignalHandler` which is
/// itself zero-sized.
///
/// Multiple `Executor` instances can coexist (via `Clone` or multiple `init()` calls)
/// and execute concurrently on different threads,
///
/// # Example
///
/// ```no_run
/// use runtime::{Executor, ModuleCache, MemoryStore, CompiledModule};
///
/// type MoveFn = unsafe extern "C" fn();
///
/// // Create a cache with a memory store
/// let store = MemoryStore::with_module("my_module".into(), CompiledModule::with_single_entry(vec![], "main"));
/// let cache = ModuleCache::new(store, 4)?;
///
/// // Get a function handle from the cache
/// let func = unsafe { cache.get_function::<MoveFn>(&"my_module".to_string(), "main")? };
///
/// // Execute with gas metering
/// let executor = Executor::init()?;
/// let result = unsafe { executor.execute(&func, 1_000_000) }?;
/// if result.completed() {
///     println!("Completed, used {} gas", result.gas_consumed);
/// } else {
///     println!("Out of gas or faulted!");
/// }
/// # Ok::<(), runtime::RuntimeError>(())
/// ```
#[derive(Clone)]
pub struct Executor {
    handler: SignalHandler,
}

impl Executor {
    /// Initialize the executor
    ///
    /// Installs the SIGTRAP signal handler. This is idempotent - calling
    /// `init()` multiple times is safe and will only install the handler once.
    ///
    /// # Errors
    ///
    /// Returns an error if the signal handler cannot be installed.
    pub fn init() -> RuntimeResult<Self> {
        let handler = SignalHandler::install()?;
        Ok(Self { handler })
    }

    /// Execute gas-instrumented native code
    ///
    /// Sets up x23 with the gas limit, calls the entry function, and
    /// returns the execution result.
    ///
    /// # Signal Handler Requirement
    ///
    /// The SIGTRAP handler installed by `Executor::init()` must remain installed.
    /// If another component replaces the handler, execution will fail silently
    /// (infinite loops instead of out-of-gas errors).
    ///
    /// In debug builds, this method verifies the handler is still installed.
    /// In release builds, use `execute_with_sigaction_check()` for explicit verification.
    ///
    /// # Type Parameters
    ///
    /// * `F` - The function pointer type (e.g., `unsafe extern "C" fn()`)
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `F` is a function pointer type (e.g., `unsafe extern "C" fn()`)
    /// - The function points to valid, verified, gas-instrumented Arm64 code
    /// - The code follows the gas instrumentation protocol (uses x23 for gas)
    pub unsafe fn execute<F: Copy>(
        &self,
        entry: &FunctionHandle<F>,
        gas_limit: u64,
    ) -> RuntimeResult<GasResult> {
        // Verify handler in debug builds only
        #[cfg(debug_assertions)]
        self.handler.verify_installed()?;

        self.execute_inner(entry.as_ptr(), gas_limit)
    }

    /// Execute with explicit signal handler verification
    ///
    /// Like `execute()`, but always verifies the SIGTRAP handler is still installed,
    /// regardless of build mode. Use this when you need guaranteed verification.
    ///
    /// # Signal Handler Requirement
    ///
    /// The SIGTRAP handler installed by `Executor::init()` must remain installed.
    /// If another component replaces the handler, this method will return an error.
    ///
    /// # Type Parameters
    ///
    /// * `F` - The function pointer type (e.g., `unsafe extern "C" fn()`)
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `F` is a function pointer type (e.g., `unsafe extern "C" fn()`)
    /// - The function points to valid, verified, gas-instrumented Arm64 code
    /// - The code follows the gas instrumentation protocol (uses x23 for gas)
    pub unsafe fn execute_with_sigaction_check<F: Copy>(
        &self,
        entry: &FunctionHandle<F>,
        gas_limit: u64,
    ) -> RuntimeResult<GasResult> {
        self.handler.verify_installed()?;
        self.execute_inner(entry.as_ptr(), gas_limit)
    }

    /// Inner execution logic (shared by both execute methods)
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `F` is a function pointer type
    /// - `entry` points to valid, gas-instrumented Arm64 code
    unsafe fn execute_inner<F: Copy>(&self, entry: F, gas_limit: u64) -> RuntimeResult<GasResult> {
        // Validate gas limit is within practical bounds
        if gas_limit > MAX_GAS_LIMIT {
            return Err(RuntimeError::GasLimitTooLarge { limit: gas_limit });
        }

        // Execute with gas tracking (internally uses i64 for sign bit check)
        // SP is saved inside the asm block for fault recovery
        set_in_move_execution(true);
        let raw_remaining = Self::execute_with_gas(entry, gas_limit as i64);
        set_in_move_execution(false);

        // Check for memory fault first (one TLS read - fast path if no fault)
        if take_fault() {
            return Ok(GasResult {
                status: ExecutionStatus::Fault,
                gas_consumed: gas_limit, // Assume all gas consumed on fault
                gas_remaining: 0,
            });
        }

        // Out-of-gas is detected by checking the sign of the gas counter
        let out_of_gas = raw_remaining < 0;

        // Clamp negative values to 0 for the public API
        let gas_remaining = raw_remaining.max(0) as u64;

        Ok(GasResult {
            status: if out_of_gas {
                ExecutionStatus::OutOfGas
            } else {
                ExecutionStatus::Completed
            },
            gas_consumed: gas_limit.saturating_sub(gas_remaining),
            gas_remaining,
        })
    }

    /// Execute the function with gas counter in x23
    ///
    /// This function:
    /// 1. Saves x23 to the stack (callee-saved, must preserve for caller)
    /// 2. Saves SP to TLS (for fault recovery - must be after our stack push)
    /// 3. Sets x23 to the gas limit
    /// 4. Computes and saves the return address (label `2:`) to TLS
    /// 5. Calls the entry function
    /// 6. Reads the remaining gas from x23
    /// 7. Restores x23 from the stack
    ///
    /// Returns the remaining gas value from x23 after execution.
    ///
    /// ## Fault Recovery
    ///
    /// If a memory fault (SIGSEGV/SIGBUS) occurs during execution:
    /// 1. Signal handler records the fault in TLS
    /// 2. Signal handler restores SP to the saved value
    /// 3. Signal handler redirects PC to the saved return address (label `2:`)
    /// 4. Execution resumes at `mov x8, x23` — no LR dependency
    /// 5. `ldr x23, [sp], #16` correctly restores x23 because SP was restored
    ///    to the value it had after our `str x23, [sp, #-16]!`
    ///
    /// This approach avoids relying on LR (x30), which gets clobbered by
    /// nested `bl` calls inside Move code. The return address is computed
    /// with `adr` before `blr {entry}` and saved to TLS.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `F` is a function pointer type (e.g., `unsafe extern "C" fn()`)
    /// - `entry` points to valid, callable Arm64 code
    #[cfg(target_arch = "aarch64")]
    #[inline(never)]
    unsafe fn execute_with_gas<F: Copy>(entry: F, gas_limit: i64) -> i64 {
        // Convert function pointer to raw pointer for inline asm
        let entry_ptr: *const () = std::mem::transmute_copy(&entry);
        let gas_remaining: i64;
        let sp_ptr = saved_sp_ptr(); // Get TLS address for SP save
        let ret_ptr = saved_return_pc_ptr(); // Get TLS address for return PC save

        asm!(
            // Save x23 to stack (callee-saved, must preserve for our caller)
            "str x23, [sp, #-16]!",
            // Save SP to memory at sp_ptr *after* our push - this is the SP that fault handler restores
            // x10 is used as scratch (reserved via out("x10") below to prevent
            // the compiler from allocating it to any in(reg) input)
            "mov x10, sp",
            "str x10, [{sp_ptr}]",
            // Set gas limit
            "mov x23, {gas_limit}",
            // Compute return address (label 2f) and save to TLS.
            // The signal handler will redirect PC here on fault, bypassing LR.
            "adr x10, 2f",
            "str x10, [{ret_ptr}]",
            // Call the function
            "blr {entry}",
            // Return point — signal handler sets PC here on fault
            "2:",
            // Read remaining gas into x8 (will be our output)
            "mov x8, x23",
            // Restore x23 from stack
            "ldr x23, [sp], #16",
            gas_limit = in(reg) gas_limit,
            entry = in(reg) entry_ptr,
            sp_ptr = in(reg) sp_ptr,
            ret_ptr = in(reg) ret_ptr,
            // x10 is used as scratch — out("x10") reserves it so the compiler
            // won't allocate it for any in(reg) input
            out("x10") _,
            // Clobbers: all caller-saved registers (function call)
            clobber_abi("C"),
            // x8 is our output register (explicit, as required by clobber_abi)
            out("x8") gas_remaining,
        );

        gas_remaining
    }

    /// Fallback for non-aarch64 platforms (for compilation only)
    #[cfg(not(target_arch = "aarch64"))]
    #[inline(never)]
    unsafe fn execute_with_gas<F: Copy>(_entry: F, _gas_limit: i64) -> i64 {
        unimplemented!("execute_with_gas is only supported on aarch64");
    }
}
