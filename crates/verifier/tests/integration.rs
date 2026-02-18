//! Integration tests for verifier
//!
//! Tests the full pipeline: assembly → object file → decode → verify.
//!
//! Key tests:
//! - Raw (uninstrumented) code should FAIL verification (missing gas checks)
//! - Instrumented code should PASS verification
//! - Stack depth verification works with real assembled code

use std::process::Command;

use instrumenter::{instrument, parser};
use verifier::{GasEffect, VerificationError, Verifier, decode_instructions};
use object::{Object, ObjectSection};
use tempfile::TempDir;

const SIMPLE_LOOP_ASM: &str = include_str!("../../../tests/asm_samples/simple_loop.s");
const NESTED_LOOPS_ASM: &str = include_str!("../../../tests/asm_samples/nested_loops.s");
const FUNCTION_CALL_ASM: &str = include_str!("../../../tests/asm_samples/function_call.s");

/// Assembles the given assembly source and returns the code section bytes.
fn assemble(source: &str) -> Vec<u8> {
    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let asm_path = temp_dir.path().join("test.s");
    let obj_path = temp_dir.path().join("test.o");

    std::fs::write(&asm_path, source).expect("failed to write asm");

    let status = Command::new("as")
        .args(["-o", obj_path.to_str().unwrap(), asm_path.to_str().unwrap()])
        .status()
        .expect("failed to run assembler");

    assert!(status.success(), "assembler failed");

    let data = std::fs::read(&obj_path).expect("failed to read object file");
    let file = object::File::parse(&*data).expect("failed to parse object file");

    let text_section = file
        .section_by_name("__text")
        .or_else(|| file.section_by_name(".text"))
        .expect("no code section found");

    text_section.data().expect("failed to read code").to_vec()
}

/// Instruments the assembly using instrumenter, then assembles it.
fn instrument_and_assemble(source: &str) -> Vec<u8> {
    let asm = parser::ParsedAssembly::parse(source);
    let cfg_result = instrumenter::build_cfg(&asm).expect("CFG build failed");
    let instrumented = instrument::instrument(asm.lines(), &cfg_result).unwrap();

    assemble(&instrumented)
}

// Raw code verification (should FAIL - missing gas checks)

#[test]
fn test_raw_simple_loop_fails_verification() {
    let code = assemble(SIMPLE_LOOP_ASM);
    let instructions = decode_instructions(&code).expect("decode failed");
    let result = Verifier::new(&instructions).verify();

    assert!(
        !result.is_ok(),
        "raw code should fail verification (no gas checks)"
    );

    // Should have malformed gas check error (ret is now allowed, not flagged)
    assert!(
        result
            .errors()
            .iter()
            .any(|e| matches!(e, VerificationError::MissingGasCheck { .. }
                    | VerificationError::GasSequenceUnexpectedInstruction { .. }
                    | VerificationError::GasSequenceBadTarget { .. }))
    );
}

#[test]
fn test_raw_nested_loops_fails_verification() {
    let code = assemble(NESTED_LOOPS_ASM);
    let instructions = decode_instructions(&code).expect("decode failed");
    let result = Verifier::new(&instructions).verify();

    assert!(
        !result.is_ok(),
        "raw code should fail verification (no gas checks)"
    );

    // Should have malformed gas check errors for both back-edges
    let malformed_gas_checks: Vec<_> = result
        .errors()
        .iter()
        .filter(|e| matches!(e, VerificationError::MissingGasCheck { .. }
                    | VerificationError::GasSequenceUnexpectedInstruction { .. }
                    | VerificationError::GasSequenceBadTarget { .. }))
        .collect();

    assert_eq!(
        malformed_gas_checks.len(),
        2,
        "expected two malformed gas check errors (one per back-edge)"
    );
}

// Instrumented code verification

#[test]
fn test_instrumented_simple_loop_fully_passes() {
    let code = instrument_and_assemble(SIMPLE_LOOP_ASM);
    let instructions = decode_instructions(&code).expect("decode failed");
    let result = Verifier::new(&instructions).verify();

    // With ret now allowed, instrumented code should fully pass
    assert!(
        result.is_ok(),
        "instrumented simple loop should pass all checks: {:?}",
        result.errors()
    );
}

#[test]
fn test_instrumented_nested_loops_gas_checks_present() {
    let code = instrument_and_assemble(NESTED_LOOPS_ASM);
    let instructions = decode_instructions(&code).expect("decode failed");
    let result = Verifier::new(&instructions).verify();

    // No malformed gas check errors
    assert!(
        !result
            .errors()
            .iter()
            .any(|e| matches!(e, VerificationError::MissingGasCheck { .. }
                    | VerificationError::GasSequenceUnexpectedInstruction { .. }
                    | VerificationError::GasSequenceBadTarget { .. })),
        "instrumented code should have valid gas checks for all back-edges"
    );
}

#[test]
fn test_stack_depth_within_budget() {
    // function_call.s has bl + stack frames (stp/ldp), should pass default budget
    let code = instrument_and_assemble(FUNCTION_CALL_ASM);
    let instructions = decode_instructions(&code).expect("decode failed");
    let result = Verifier::new(&instructions).verify();

    assert!(
        !result
            .errors()
            .iter()
            .any(|e| matches!(e, VerificationError::StackDepthExceeded { .. })),
        "function_call.s stack depth should be within default budget: {:?}",
        result.errors()
    );
}

#[test]
fn test_stack_depth_exceeded_with_small_budget() {
    // Same code but with a very small budget — function_call.s has stp [sp, #-16]!
    // so the caller frame is at least 16 bytes. Budget of 8 should fail.
    let code = instrument_and_assemble(FUNCTION_CALL_ASM);
    let instructions = decode_instructions(&code).expect("decode failed");
    let result = Verifier::with_budgets(&instructions, 8, 1_000_000_000).verify();

    assert!(
        result
            .errors()
            .iter()
            .any(|e| matches!(e, VerificationError::StackDepthExceeded { .. })),
        "function_call.s with budget=8 should fail StackDepthExceeded: {:?}",
        result.errors()
    );
}

#[test]
fn test_decode_raw_simple_loop() {
    let code = assemble(SIMPLE_LOOP_ASM);
    let instructions = decode_instructions(&code).expect("decode failed");

    // simple_loop.s has: mov, mov, add, cmp, b.lt, ret = 6 instructions
    assert_eq!(instructions.len(), 6);
}

#[test]
fn test_decode_instrumented_simple_loop() {
    let code = instrument_and_assemble(SIMPLE_LOOP_ASM);
    let instructions = decode_instructions(&code).expect("decode failed");

    // After instrumentation: original 6 + gas check (sub, tbz, brk) = 9
    assert_eq!(instructions.len(), 9);
}

#[test]
fn test_decode_instrumented_nested_loops() {
    let code = instrument_and_assemble(NESTED_LOOPS_ASM);
    let instructions = decode_instructions(&code).expect("decode failed");

    // Should have 2 gas check sequences (one per back-edge)
    let gas_decrements = instructions
        .iter()
        .filter(|i| matches!(GasEffect::from(*i), GasEffect::Decrement(_)))
        .count();

    assert_eq!(gas_decrements, 2, "expected two gas decrements");
}
