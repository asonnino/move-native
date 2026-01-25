//! Entry point for executing gas-instrumented native code
//!
//! The execute function sets up the gas counter in x23, calls the native
//! function, and returns execution results including gas consumption.

use std::arch::asm;

use crate::{
    error::RuntimeResult,
    signal::{install_handler, is_out_of_gas, reset_out_of_gas},
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

/// Execute gas-instrumented native code
///
/// Sets up x23 with the gas limit, installs the SIGTRAP handler,
/// calls the entry function, and returns the execution result.
///
/// # Safety
///
/// The caller must ensure:
/// - `entry` points to valid, verified, gas-instrumented Arm64 code
/// - The code follows the gas instrumentation protocol (uses x23 for gas)
/// - No other threads are executing gas-instrumented code concurrently
///
/// # Example
///
/// ```ignore
/// let module = NativeModule::load("my_module.dylib")?;
/// let entry = module.get_function::<unsafe extern "C" fn()>("my_function")?;
/// let result = unsafe { execute(entry, 1_000_000) }?;
/// if result.completed {
///     println!("Completed, used {} gas", result.gas_consumed);
/// } else {
///     println!("Out of gas!");
/// }
/// ```
pub unsafe fn execute(entry: unsafe extern "C" fn(), gas_limit: u64) -> RuntimeResult<GasResult> {
    // Install the signal handler (idempotent)
    install_handler()?;

    // Reset the out-of-gas flag
    reset_out_of_gas();

    // Execute with gas tracking (internally uses i64 for sign bit check)
    let raw_remaining = execute_with_gas(entry, gas_limit as i64);

    // Clamp negative values to 0 for the public API
    let gas_remaining = raw_remaining.max(0) as u64;

    Ok(GasResult {
        completed: !is_out_of_gas(),
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
#[cfg(target_arch = "aarch64")]
#[inline(never)]
unsafe fn execute_with_gas(entry: unsafe extern "C" fn(), gas_limit: i64) -> i64 {
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
        entry = in(reg) entry,
        // Clobbers: all caller-saved registers (function call)
        clobber_abi("C"),
        // x8 is our output register
        out("x8") gas_remaining,
    );

    gas_remaining
}

/// Fallback for non-aarch64 platforms (for compilation only)
#[cfg(not(target_arch = "aarch64"))]
unsafe fn execute_with_gas(_entry: unsafe extern "C" fn(), _gas_limit: i64) -> i64 {
    panic!("execute_with_gas is only supported on aarch64");
}
