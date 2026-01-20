//! Integration tests for the runtime crate
//!
//! Tests the full pipeline: instrument → assemble → link → load → execute.

use std::path::Path;
use std::process::Command;

use gas_instrument::{instrument, parser};
use runtime::{execute, NativeModule};
use tempfile::TempDir;

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

/// Links an object file into a shared library.
#[cfg(target_os = "macos")]
fn link_shared_lib(obj_path: &Path, lib_path: &Path) {
    // Use clang to link - it handles SDK paths automatically
    let status = Command::new("clang")
        .args([
            "-shared",
            "-arch",
            "arm64",
            "-o",
            lib_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
        ])
        .status()
        .expect("failed to run linker");

    assert!(status.success(), "linker failed: clang -shared");
}

/// Links an object file into a shared library.
#[cfg(target_os = "linux")]
fn link_shared_lib(obj_path: &Path, lib_path: &Path) {
    let status = Command::new("ld")
        .args([
            "-shared",
            "-o",
            lib_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
        ])
        .status()
        .expect("failed to run linker");

    assert!(status.success(), "linker failed: ld -shared");
}

/// Creates an instrumented shared library from assembly source.
/// Returns the temp directory (to keep files alive) and path to the library.
///
/// `symbol_name` is the dlsym-style symbol name (without leading underscore on macOS).
/// The function automatically adds the underscore prefix when checking nm output on macOS.
fn build_instrumented_lib(source: &str, symbol_name: &str) -> (TempDir, std::path::PathBuf) {
    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let obj_path = temp_dir.path().join("test.o");

    #[cfg(target_os = "macos")]
    let lib_path = temp_dir.path().join("test.dylib");
    #[cfg(target_os = "linux")]
    let lib_path = temp_dir.path().join("test.so");
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    let lib_path = temp_dir.path().join("test.so");

    // Instrument the assembly
    let instrumented = instrument_asm(source);

    // Assemble
    assemble(&instrumented, &obj_path);

    // Link into shared library
    link_shared_lib(&obj_path, &lib_path);

    // Verify the symbol exists in nm output
    // On macOS, nm shows symbols with leading underscore, but dlsym expects without
    #[cfg(target_os = "macos")]
    let nm_symbol_name = format!("_{}", symbol_name);
    #[cfg(not(target_os = "macos"))]
    let nm_symbol_name = symbol_name.to_string();

    let output = Command::new("nm")
        .arg(&lib_path)
        .output()
        .expect("failed to run nm");
    let nm_output = String::from_utf8_lossy(&output.stdout);
    assert!(
        nm_output.contains(&nm_symbol_name),
        "symbol {} not found in library. nm output:\n{}",
        nm_symbol_name,
        nm_output
    );

    (temp_dir, lib_path)
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_execute_with_sufficient_gas() {
    let (_temp_dir, lib_path) = build_instrumented_lib(SIMPLE_LOOP_ASM, "simple_loop");

    let module = NativeModule::load(&lib_path).expect("failed to load module");
    let entry = unsafe {
        module
            .get_function::<unsafe extern "C" fn()>("simple_loop")
            .expect("failed to get function")
    };

    // Execute with plenty of gas (loop runs 1000 times, each iteration ~3 gas)
    let result = unsafe { execute(*entry, 100_000) }.expect("execute failed");

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
    let (_temp_dir, lib_path) = build_instrumented_lib(SIMPLE_LOOP_ASM, "simple_loop");

    let module = NativeModule::load(&lib_path).expect("failed to load module");
    let entry = unsafe {
        module
            .get_function::<unsafe extern "C" fn()>("simple_loop")
            .expect("failed to get function")
    };

    // Execute with very little gas (not enough to complete the loop)
    let result = unsafe { execute(*entry, 10) }.expect("execute failed");

    assert!(
        !result.completed,
        "should run out of gas with only 10 gas units"
    );
    // Gas remaining may be negative when out of gas
    assert!(
        result.gas_remaining <= 0,
        "gas_remaining should be zero or negative after out-of-gas"
    );
}

#[test]
fn test_symbol_not_found() {
    let (_temp_dir, lib_path) = build_instrumented_lib(SIMPLE_LOOP_ASM, "simple_loop");

    let module = NativeModule::load(&lib_path).expect("failed to load module");
    let result = unsafe { module.get_function::<unsafe extern "C" fn()>("nonexistent_symbol") };

    assert!(result.is_err());
    match result.unwrap_err() {
        runtime::RuntimeError::SymbolNotFound { symbol } => {
            assert_eq!(symbol, "nonexistent_symbol");
        }
        e => panic!("expected SymbolNotFound error, got: {:?}", e),
    }
}

#[test]
fn test_load_nonexistent_library() {
    let result = NativeModule::load("/nonexistent/path/to/library.dylib");
    assert!(result.is_err());
    match result.unwrap_err() {
        runtime::RuntimeError::LoadError { .. } => {}
        e => panic!("expected LoadError, got: {:?}", e),
    }
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn test_multiple_executions() {
    let (_temp_dir, lib_path) = build_instrumented_lib(SIMPLE_LOOP_ASM, "simple_loop");

    let module = NativeModule::load(&lib_path).expect("failed to load module");
    let entry = unsafe {
        module
            .get_function::<unsafe extern "C" fn()>("simple_loop")
            .expect("failed to get function")
    };

    // Execute multiple times to ensure state is properly reset between executions
    for i in 0..3 {
        let result = unsafe { execute(*entry, 100_000) }.expect("execute failed");
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
    let (_temp_dir, lib_path) = build_instrumented_lib(SIMPLE_LOOP_ASM, "simple_loop");

    let module = NativeModule::load(&lib_path).expect("failed to load module");
    let entry = unsafe {
        module
            .get_function::<unsafe extern "C" fn()>("simple_loop")
            .expect("failed to get function")
    };

    // First execution: out of gas
    let result1 = unsafe { execute(*entry, 10) }.expect("execute failed");
    assert!(!result1.completed, "should run out of gas");

    // Second execution: should succeed (state properly reset)
    let result2 = unsafe { execute(*entry, 100_000) }.expect("execute failed");
    assert!(
        result2.completed,
        "should complete after previous out-of-gas"
    );
}
