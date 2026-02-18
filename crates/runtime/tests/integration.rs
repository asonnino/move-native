// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the runtime crate
//!
//! Tests the full pipeline: instrument → assemble → extract binary → load → execute.

use std::{path::Path, process::Command};

use instrumenter::{instrument, parser};
use object::{Object, ObjectSection};
use runtime::{CompiledModule, ExecutionStatus, Executor, MemoryStore, ModuleCache};
use tempfile::TempDir;

/// The function type for all test functions
type TestFn = unsafe extern "C" fn();

const SIMPLE_LOOP_ASM: &str = include_str!("../../../tests/asm_samples/simple_loop.s");
const NESTED_LOOPS_ASM: &str = include_str!("../../../tests/asm_samples/nested_loops.s");
const FORWARD_ONLY_ASM: &str = include_str!("../../../tests/asm_samples/forward_only.s");
const FUNCTION_CALL_ASM: &str = include_str!("../../../tests/asm_samples/function_call.s");
const CBZ_LOOP_ASM: &str = include_str!("../../../tests/asm_samples/cbz_loop.s");
const UNCONDITIONAL_LOOP_ASM: &str =
    include_str!("../../../tests/asm_samples/unconditional_loop.s");
const MULTIPLE_FUNCTIONS_ASM: &str =
    include_str!("../../../tests/asm_samples/multiple_functions.s");
const LARGE_BLOCK_ASM: &str = include_str!("../../../tests/asm_samples/large_block.s");
const NULL_DEREF_ASM: &str = include_str!("../../../tests/asm_samples/null_deref.s");
const UNMAPPED_JUMP_ASM: &str = include_str!("../../../tests/asm_samples/unmapped_jump.s");
const STACK_THEN_FAULT_ASM: &str = include_str!("../../../tests/asm_samples/stack_then_fault.s");
const NESTED_FAULT_ASM: &str = include_str!("../../../tests/asm_samples/nested_fault.s");

/// Instruments the assembly using instrumenter.
fn instrument_asm(source: &str) -> String {
    let asm = parser::ParsedAssembly::parse(source);
    let cfg_result = instrumenter::build_cfg(&asm).expect("CFG build failed");
    instrument::instrument(asm.lines(), &cfg_result).unwrap()
}

/// Assembles the given assembly source into an object file.
fn assemble(source: &str, obj_path: &Path) {
    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let asm_path = temp_dir.path().join("test.s");

    std::fs::write(&asm_path, source).expect("failed to write asm");

    let status = Command::new("as")
        .args(["-o", obj_path.to_str().unwrap(), asm_path.to_str().unwrap()])
        .status()
        .expect("failed to run assembler");

    assert!(status.success(), "assembler failed");
}

/// Extracts the text section from an object file using the `object` crate.
fn extract_text_section(obj_path: &Path) -> Vec<u8> {
    let data = std::fs::read(obj_path).expect("failed to read object file");
    let file = object::File::parse(&*data).expect("failed to parse object file");

    // Find the text section (named "__text" on macOS, ".text" on Linux)
    for section in file.sections() {
        let name = section.name().unwrap_or("");
        if name == "__text" || name == ".text" {
            return section
                .data()
                .expect("failed to read text section")
                .to_vec();
        }
    }

    panic!("text section not found in object file");
}

/// Creates an instrumented binary from assembly source.
/// Returns the raw bytes of the instrumented code.
fn build_instrumented_binary(source: &str) -> Vec<u8> {
    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let obj_path = temp_dir.path().join("test.o");

    // Instrument the assembly
    let instrumented = instrument_asm(source);

    // Assemble to object file
    assemble(&instrumented, &obj_path);

    // Extract text section using the object crate
    extract_text_section(&obj_path)
}

/// Assembles without instrumentation (for fault-inducing code that doesn't need gas checks)
fn build_uninstrumented_binary(source: &str) -> Vec<u8> {
    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let obj_path = temp_dir.path().join("test.o");

    // Assemble directly without instrumentation
    assemble(source, &obj_path);

    // Extract text section
    extract_text_section(&obj_path)
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_execute_with_sufficient_gas() {
    let code = build_instrumented_binary(SIMPLE_LOOP_ASM);
    let module = CompiledModule::with_single_entry(code, "simple_loop");

    let store = MemoryStore::with_module("test".to_string(), module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let cached_fn = unsafe {
        cache
            .get_function::<TestFn>(&"test".to_string(), "simple_loop")
            .expect("failed to get function")
    };

    let executor = Executor::init().expect("failed to create executor");

    // Execute with plenty of gas (loop runs 1000 times, each iteration ~3 gas)
    let result = unsafe { executor.execute(&cached_fn, 100_000) }.expect("execute failed");

    assert!(
        result.completed(),
        "should complete with sufficient gas, but got: {:?}",
        result
    );
    assert!(
        result.gas_consumed > 0,
        "should consume some gas, got: {}",
        result.gas_consumed
    );
    assert!(
        result.gas_remaining > 0,
        "should have gas remaining, got: {}",
        result.gas_remaining
    );
    assert_eq!(
        result.gas_consumed + result.gas_remaining,
        100_000,
        "gas_consumed + gas_remaining should equal initial gas"
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_execute_with_insufficient_gas() {
    let code = build_instrumented_binary(SIMPLE_LOOP_ASM);
    let module = CompiledModule::with_single_entry(code, "simple_loop");

    let store = MemoryStore::with_module("test".to_string(), module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let cached_fn = unsafe {
        cache
            .get_function::<TestFn>(&"test".to_string(), "simple_loop")
            .expect("failed to get function")
    };

    let executor = Executor::init().expect("failed to create executor");

    // Execute with very little gas (not enough to complete the loop)
    let result = unsafe { executor.execute(&cached_fn, 10) }.expect("execute failed");

    assert!(
        !result.completed(),
        "should run out of gas with only 10 gas units"
    );
    assert_eq!(
        result.gas_remaining, 0,
        "gas_remaining should be zero after out-of-gas"
    );
}

#[test]
fn test_symbol_not_found() {
    let code = vec![0x40, 0x05, 0x80, 0xd2, 0xc0, 0x03, 0x5f, 0xd6]; // mov x0, #42; ret
    let module = CompiledModule::with_single_entry(code, "main");

    let store = MemoryStore::with_module("test".to_string(), module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let result = unsafe { cache.get_function::<TestFn>(&"test".to_string(), "nonexistent_symbol") };

    assert!(result.is_err());
    match result.unwrap_err() {
        runtime::RuntimeError::FunctionNotFound { name } => {
            assert_eq!(name, "nonexistent_symbol");
        }
        e => panic!("expected FunctionNotFound error, got: {:?}", e),
    }
}

#[test]
fn test_load_nonexistent_library() {
    let store = MemoryStore::<String>::new();
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let result = unsafe { cache.get_function::<TestFn>(&"nonexistent".to_string(), "func") };

    assert!(result.is_err());
    match result.unwrap_err() {
        runtime::RuntimeError::ModuleNotFound { .. } => {}
        e => panic!("expected ModuleNotFound, got: {:?}", e),
    }
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_multiple_executions() {
    let code = build_instrumented_binary(SIMPLE_LOOP_ASM);
    let module = CompiledModule::with_single_entry(code, "simple_loop");

    let store = MemoryStore::with_module("test".to_string(), module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let cached_fn = unsafe {
        cache
            .get_function::<TestFn>(&"test".to_string(), "simple_loop")
            .expect("failed to get function")
    };

    let executor = Executor::init().expect("failed to create executor");

    // Execute multiple times to ensure state is properly reset between executions
    for i in 0..3 {
        let result = unsafe { executor.execute(&cached_fn, 100_000) }.expect("execute failed");
        assert!(
            result.completed(),
            "execution {} should complete with sufficient gas",
            i
        );
    }
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_out_of_gas_then_successful() {
    let code = build_instrumented_binary(SIMPLE_LOOP_ASM);
    let module = CompiledModule::with_single_entry(code, "simple_loop");

    let store = MemoryStore::with_module("test".to_string(), module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let cached_fn = unsafe {
        cache
            .get_function::<TestFn>(&"test".to_string(), "simple_loop")
            .expect("failed to get function")
    };

    let executor = Executor::init().expect("failed to create executor");

    // First execution: out of gas
    let result1 = unsafe { executor.execute(&cached_fn, 10) }.expect("execute failed");
    assert!(!result1.completed(), "should run out of gas");

    // Second execution: should succeed (state properly reset)
    let result2 = unsafe { executor.execute(&cached_fn, 100_000) }.expect("execute failed");
    assert!(
        result2.completed(),
        "should complete after previous out-of-gas"
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_nested_loops() {
    let code = build_instrumented_binary(NESTED_LOOPS_ASM);
    let module = CompiledModule::with_single_entry(code, "nested_loops");

    let store = MemoryStore::with_module("test".to_string(), module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let cached_fn = unsafe {
        cache
            .get_function::<TestFn>(&"test".to_string(), "nested_loops")
            .expect("failed to get function")
    };

    let executor = Executor::init().expect("failed to create executor");

    // Nested loops: outer=10, inner=10 -> 100 total iterations
    // Each iteration uses a few gas units
    let result = unsafe { executor.execute(&cached_fn, 10_000) }.expect("execute failed");

    assert!(
        result.completed(),
        "nested loops should complete with sufficient gas"
    );
    assert!(
        result.gas_consumed > 0,
        "should consume gas for nested iterations"
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_forward_only_no_gas_consumed_in_loops() {
    // Forward-only code has no back-edges, so no gas checks are inserted.
    // The code should complete with minimal gas usage (just the entry overhead).
    let code = build_instrumented_binary(FORWARD_ONLY_ASM);
    let module = CompiledModule::with_single_entry(code, "forward_only");

    let store = MemoryStore::with_module("test".to_string(), module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let cached_fn = unsafe {
        cache
            .get_function::<TestFn>(&"test".to_string(), "forward_only")
            .expect("failed to get function")
    };

    let executor = Executor::init().expect("failed to create executor");

    // Even with very little gas, forward-only code should complete
    // because there are no gas checks (no back-edges)
    let result = unsafe { executor.execute(&cached_fn, 10) }.expect("execute failed");

    assert!(
        result.completed(),
        "forward-only code should complete even with minimal gas"
    );
    // Gas consumed should be 0 since there are no back-edges to trigger checks
    assert_eq!(
        result.gas_consumed, 0,
        "forward-only code should consume no gas (no back-edges)"
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_function_call_preserves_gas_register() {
    // Tests that x23 (gas register) is preserved across bl calls
    let code = build_instrumented_binary(FUNCTION_CALL_ASM);
    let module = CompiledModule::with_single_entry(code, "loop_with_call");

    let store = MemoryStore::with_module("test".to_string(), module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let cached_fn = unsafe {
        cache
            .get_function::<TestFn>(&"test".to_string(), "loop_with_call")
            .expect("failed to get function")
    };

    let executor = Executor::init().expect("failed to create executor");

    // Loop runs 100 times with function call each iteration
    let result = unsafe { executor.execute(&cached_fn, 10_000) }.expect("execute failed");

    assert!(
        result.completed(),
        "loop with function calls should complete"
    );
    assert!(
        result.gas_consumed > 0,
        "should consume gas in loop iterations"
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_cbz_loop() {
    let code = build_instrumented_binary(CBZ_LOOP_ASM);
    let module = CompiledModule::with_single_entry(code, "cbz_loop");

    let store = MemoryStore::with_module("test".to_string(), module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let cached_fn = unsafe {
        cache
            .get_function::<TestFn>(&"test".to_string(), "cbz_loop")
            .expect("failed to get function")
    };

    let executor = Executor::init().expect("failed to create executor");

    // Loop counts down from 10 to 0
    let result = unsafe { executor.execute(&cached_fn, 1_000) }.expect("execute failed");

    assert!(result.completed(), "cbnz loop should complete");
    assert!(result.gas_consumed > 0, "should consume gas in cbnz loop");
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_unconditional_back_edge() {
    let code = build_instrumented_binary(UNCONDITIONAL_LOOP_ASM);
    let module = CompiledModule::with_single_entry(code, "unconditional_loop");

    let store = MemoryStore::with_module("test".to_string(), module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let cached_fn = unsafe {
        cache
            .get_function::<TestFn>(&"test".to_string(), "unconditional_loop")
            .expect("failed to get function")
    };

    let executor = Executor::init().expect("failed to create executor");

    // Loop runs 100 times
    let result = unsafe { executor.execute(&cached_fn, 10_000) }.expect("execute failed");

    assert!(
        result.completed(),
        "unconditional back-edge loop should complete"
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_multiple_functions_same_module() {
    let code = build_instrumented_binary(MULTIPLE_FUNCTIONS_ASM);

    // func_add is at offset 0 (first function in the file)
    let module = CompiledModule::with_single_entry(code, "func_add");

    let store = MemoryStore::with_module("test".to_string(), module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let cached_fn = unsafe {
        cache
            .get_function::<TestFn>(&"test".to_string(), "func_add")
            .expect("failed to get function")
    };

    let executor = Executor::init().expect("failed to create executor");

    let result = unsafe { executor.execute(&cached_fn, 10_000) }.expect("execute failed");

    assert!(result.completed(), "func_add should complete");
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_large_basic_block_gas_count() {
    let code = build_instrumented_binary(LARGE_BLOCK_ASM);
    let module = CompiledModule::with_single_entry(code, "large_block");

    let store = MemoryStore::with_module("test".to_string(), module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let cached_fn = unsafe {
        cache
            .get_function::<TestFn>(&"test".to_string(), "large_block")
            .expect("failed to get function")
    };

    let executor = Executor::init().expect("failed to create executor");

    // Loop runs 10 times, each iteration has 20 instructions
    // Total gas should be roughly 10 * 20 = 200
    let result = unsafe { executor.execute(&cached_fn, 1_000) }.expect("execute failed");

    assert!(result.completed(), "large block loop should complete");
    // Verify substantial gas was consumed (at least 100, likely ~200)
    assert!(
        result.gas_consumed >= 100,
        "large block should consume significant gas, got: {}",
        result.gas_consumed
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_large_block_out_of_gas() {
    let code = build_instrumented_binary(LARGE_BLOCK_ASM);
    let module = CompiledModule::with_single_entry(code, "large_block");

    let store = MemoryStore::with_module("test".to_string(), module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let cached_fn = unsafe {
        cache
            .get_function::<TestFn>(&"test".to_string(), "large_block")
            .expect("failed to get function")
    };

    let executor = Executor::init().expect("failed to create executor");

    // Give less gas than needed for one full iteration (20 instructions)
    // This should trigger out-of-gas on the first back-edge check
    let result = unsafe { executor.execute(&cached_fn, 15) }.expect("execute failed");

    assert!(
        !result.completed(),
        "should run out of gas with only 15 units for 20-instruction block"
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_null_deref_returns_fault() {
    let code = build_uninstrumented_binary(NULL_DEREF_ASM);
    let module = CompiledModule::with_single_entry(code, "null_deref");

    let store = MemoryStore::with_module("test".to_string(), module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let cached_fn = unsafe {
        cache
            .get_function::<TestFn>(&"test".to_string(), "null_deref")
            .expect("failed to get function")
    };

    let executor = Executor::init().expect("failed to create executor");

    let result = unsafe { executor.execute(&cached_fn, 1_000_000) }.expect("execute failed");

    assert_eq!(
        result.status,
        ExecutionStatus::Fault,
        "null pointer dereference should return Fault status"
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_unmapped_jump_returns_fault() {
    let code = build_uninstrumented_binary(UNMAPPED_JUMP_ASM);
    let module = CompiledModule::with_single_entry(code, "unmapped_jump");

    let store = MemoryStore::with_module("test".to_string(), module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let cached_fn = unsafe {
        cache
            .get_function::<TestFn>(&"test".to_string(), "unmapped_jump")
            .expect("failed to get function")
    };

    let executor = Executor::init().expect("failed to create executor");

    let result = unsafe { executor.execute(&cached_fn, 1_000_000) }.expect("execute failed");

    assert_eq!(
        result.status,
        ExecutionStatus::Fault,
        "jump to unmapped address should return Fault status"
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_fault_does_not_affect_subsequent_execution() {
    let executor = Executor::init().expect("failed to create executor");

    // First: cause a fault
    let bad_code = build_uninstrumented_binary(NULL_DEREF_ASM);
    let bad_module = CompiledModule::with_single_entry(bad_code, "null_deref");
    let bad_store = MemoryStore::with_module("bad".to_string(), bad_module);
    let bad_cache = ModuleCache::new(bad_store, 4).expect("failed to create cache");
    let bad_func = unsafe {
        bad_cache
            .get_function::<TestFn>(&"bad".to_string(), "null_deref")
            .expect("failed to get function")
    };

    let result = unsafe { executor.execute(&bad_func, 1_000_000) }.expect("execute failed");
    assert_eq!(
        result.status,
        ExecutionStatus::Fault,
        "first execution should fault"
    );

    // Second: normal execution should work fine
    let good_code = build_instrumented_binary(SIMPLE_LOOP_ASM);
    let good_module = CompiledModule::with_single_entry(good_code, "simple_loop");
    let good_store = MemoryStore::with_module("good".to_string(), good_module);
    let good_cache = ModuleCache::new(good_store, 4).expect("failed to create cache");
    let good_func = unsafe {
        good_cache
            .get_function::<TestFn>(&"good".to_string(), "simple_loop")
            .expect("failed to get function")
    };

    let result = unsafe { executor.execute(&good_func, 100_000) }.expect("execute failed");
    assert_eq!(
        result.status,
        ExecutionStatus::Completed,
        "execution after fault should complete normally"
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_fault_after_stack_manipulation() {
    // Tests that SP restoration works even when the faulting code
    // has modified the stack before the fault
    let code = build_uninstrumented_binary(STACK_THEN_FAULT_ASM);
    let module = CompiledModule::with_single_entry(code, "stack_then_fault");
    let store = MemoryStore::with_module("test".to_string(), module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let cached_fn = unsafe {
        cache
            .get_function::<TestFn>(&"test".to_string(), "stack_then_fault")
            .expect("failed to get function")
    };

    let executor = Executor::init().expect("failed to create executor");

    let result = unsafe { executor.execute(&cached_fn, 1_000_000) }.expect("execute failed");
    assert_eq!(
        result.status,
        ExecutionStatus::Fault,
        "fault after stack manipulation should be caught"
    );

    // Verify executor is still usable
    let simple_code = build_instrumented_binary(SIMPLE_LOOP_ASM);
    let simple_module = CompiledModule::with_single_entry(simple_code, "simple_loop");
    let simple_store = MemoryStore::with_module("simple".to_string(), simple_module);
    let simple_cache = ModuleCache::new(simple_store, 4).expect("failed to create cache");
    let simple_func = unsafe {
        simple_cache
            .get_function::<TestFn>(&"simple".to_string(), "simple_loop")
            .expect("failed to get function")
    };

    let result = unsafe { executor.execute(&simple_func, 100_000) }.expect("execute failed");
    assert_eq!(
        result.status,
        ExecutionStatus::Completed,
        "executor should still work after fault with stack manipulation"
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_nested_call_fault() {
    let code = build_uninstrumented_binary(NESTED_FAULT_ASM);
    let module = CompiledModule::with_single_entry(code, "nested_fault");

    let store = MemoryStore::with_module("test".to_string(), module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    let cached_fn = unsafe {
        cache
            .get_function::<TestFn>(&"test".to_string(), "nested_fault")
            .expect("failed to get function")
    };

    let executor = Executor::init().expect("failed to create executor");

    let result = unsafe { executor.execute(&cached_fn, 1_000_000) }.expect("execute failed");
    assert_eq!(
        result.status,
        ExecutionStatus::Fault,
        "fault inside nested bl call should return Fault status"
    );

    // Verify executor is still usable after nested-call fault
    let good_code = build_instrumented_binary(SIMPLE_LOOP_ASM);
    let good_module = CompiledModule::with_single_entry(good_code, "simple_loop");
    let good_store = MemoryStore::with_module("good".to_string(), good_module);
    let good_cache = ModuleCache::new(good_store, 4).expect("failed to create cache");
    let good_func = unsafe {
        good_cache
            .get_function::<TestFn>(&"good".to_string(), "simple_loop")
            .expect("failed to get function")
    };

    let result = unsafe { executor.execute(&good_func, 100_000) }.expect("execute failed");
    assert_eq!(
        result.status,
        ExecutionStatus::Completed,
        "executor should still work after nested-call fault"
    );
}
