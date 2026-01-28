//! Integration tests for the runtime crate
//!
//! Tests the full pipeline: instrument → assemble → extract binary → load → execute.

use std::{path::Path, process::Command};

use gas_instrument::{instrument, parser};
use object::{Object, ObjectSection};
use runtime::{CompiledModule, Executor, MemoryStore, ModuleCache};
use tempfile::TempDir;

/// The function type for all test functions
type TestFn = unsafe extern "C" fn();

const SIMPLE_LOOP_ASM: &str = include_str!("../../../tests/asm_samples/simple_loop.s");

/// Instruments the assembly using gas-instrument.
fn instrument_asm(source: &str) -> String {
    let asm = parser::ParsedAssembly::parse(source);
    let cfg_result = gas_instrument::build_cfg(&asm).expect("CFG build failed");
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
            return section.data().expect("failed to read text section").to_vec();
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
        result.completed,
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
        !result.completed,
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
            result.completed,
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
    assert!(!result1.completed, "should run out of gas");

    // Second execution: should succeed (state properly reset)
    let result2 = unsafe { executor.execute(&cached_fn, 100_000) }.expect("execute failed");
    assert!(
        result2.completed,
        "should complete after previous out-of-gas"
    );
}
