//! Executor for gas-instrumented native code
//!
//! The Executor handles signal handler installation and provides the
//! execution API for running gas-instrumented Arm64 code.

use std::arch::asm;

use crate::{
    error::{RuntimeError, RuntimeResult},
    signal::SignalHandler,
};

/// Result of executing native code
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GasResult {
    /// Whether execution completed (true) or ran out of gas (false)
    pub completed: bool,
    /// Amount of gas consumed during execution
    pub gas_consumed: u64,
    /// Remaining gas after execution (clamped to 0 if exhausted)
    pub gas_remaining: u64,
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
/// use runtime::{Executor, NativeModule};
///
/// let executor = Executor::init()?;
/// let module = NativeModule::load("my_module.dylib")?;
/// let entry = unsafe { module.get_function::<unsafe extern "C" fn()>("my_function")? };
/// let result = unsafe { executor.execute(*entry, 1_000_000) }?;
/// if result.completed {
///     println!("Completed, used {} gas", result.gas_consumed);
/// } else {
///     println!("Out of gas!");
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
    /// # Type Parameters
    ///
    /// * `F` - The function pointer type (e.g., `unsafe extern "C" fn()`)
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `F` is a function pointer type (e.g., `unsafe extern "C" fn()`)
    /// - `entry` points to valid, verified, gas-instrumented Arm64 code
    /// - The code follows the gas instrumentation protocol (uses x23 for gas)
    pub unsafe fn execute<F: Copy>(&self, entry: F, gas_limit: u64) -> RuntimeResult<GasResult> {
        // Validate gas limit fits in i64 (we use sign bit for exhaustion check)
        if gas_limit > i64::MAX as u64 {
            return Err(RuntimeError::GasLimitTooLarge { limit: gas_limit });
        }

        // Reset the out-of-gas flag
        self.handler.reset();

        // Execute with gas tracking (internally uses i64 for sign bit check)
        let raw_remaining = Self::execute_with_gas(entry, gas_limit as i64);

        // Clamp negative values to 0 for the public API
        let gas_remaining = raw_remaining.max(0) as u64;

        Ok(GasResult {
            completed: !self.handler.is_out_of_gas(),
            gas_consumed: gas_limit - gas_remaining,
            gas_remaining,
        })
    }

    /// Execute the function with gas counter in x23
    ///
    /// This function:
    /// 1. Saves x23 to the stack (callee-saved, must preserve for caller)
    /// 2. Sets x23 to the gas limit
    /// 3. Calls the entry function
    /// 4. Reads the remaining gas from x23
    /// 5. Restores x23 from the stack
    ///
    /// Returns the remaining gas value from x23 after execution.
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

        asm!(
            // Save x23 to stack (callee-saved, must preserve for our caller)
            "str x23, [sp, #-16]!",
            // Set gas limit
            "mov x23, {gas_limit}",
            // Call the function
            "blr {entry}",
            // Read remaining gas into x8
            "mov x8, x23",
            // Restore x23 from stack
            "ldr x23, [sp], #16",
            gas_limit = in(reg) gas_limit,
            entry = in(reg) entry_ptr,
            // Clobbers: all caller-saved registers (function call)
            clobber_abi("C"),
            // x8 is our output register
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
