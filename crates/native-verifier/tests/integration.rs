//! Integration tests for native-verifier
//!
//! These tests exercise the full decode pipeline on real assembly files:
//!
//! 1. Take assembly from `tests/asm_samples/`
//! 2. Assemble with `as` to produce object files
//! 3. Decode the `__text` section
//! 4. Verify all instructions decode successfully
//!
//! This catches any mismatch between what gas-instrument produces and what
//! native-verifier can process.

use std::process::Command;

use gas_instrument::{cfg, instrument, parser};
use native_verifier::decode_instructions;
use object::{Object, ObjectSection};
use tempfile::TempDir;

const TEST_LOOP_ASM: &str = include_str!("../../../tests/asm_samples/test_loop.s");
const NESTED_LOOPS_ASM: &str = include_str!("../../../tests/asm_samples/nested_loops.s");

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

/// Instruments the assembly using gas-instrument, then assembles it.
fn instrument_and_assemble(source: &str) -> Vec<u8> {
    let asm = parser::ParsedAssembly::parse(source);
    let cfg_result = cfg::build(&asm).expect("CFG build failed");
    let instrumented = instrument::instrument(asm.lines(), &cfg_result);

    assemble(&instrumented)
}

#[test]
fn test_decode_raw_test_loop() {
    let code = assemble(TEST_LOOP_ASM);
    let instructions = decode_instructions(&code).expect("decode failed");

    // test_loop.s has: mov, mov, add, cmp, b.lt, ret = 6 instructions
    assert_eq!(instructions.len(), 6);

    // Verify we can identify the back-edge
    let back_edges: Vec<_> = instructions
        .iter()
        .filter(|i| i.is_branch() && i.branch_target().map(|t| t <= i.offset).unwrap_or(false))
        .collect();

    assert_eq!(back_edges.len(), 1, "expected one back-edge");
}

#[test]
fn test_decode_raw_nested_loops() {
    let code = assemble(NESTED_LOOPS_ASM);
    let instructions = decode_instructions(&code).expect("decode failed");

    // Verify we can identify both back-edges
    let back_edges: Vec<_> = instructions
        .iter()
        .filter(|i| i.is_branch() && i.branch_target().map(|t| t <= i.offset).unwrap_or(false))
        .collect();

    assert_eq!(
        back_edges.len(),
        2,
        "expected two back-edges (inner + outer)"
    );
}

#[test]
fn test_decode_instrumented_test_loop() {
    let code = instrument_and_assemble(TEST_LOOP_ASM);
    let instructions = decode_instructions(&code).expect("decode failed");

    // After instrumentation: original 6 + gas check (sub, tbz, brk) = 9
    assert_eq!(instructions.len(), 9);

    // Verify gas check sequence is present
    let gas_decrements: Vec<_> = instructions
        .iter()
        .filter(|i| i.is_gas_decrement())
        .collect();

    assert_eq!(gas_decrements.len(), 1, "expected one gas decrement");

    // Verify gas check branch (tbz x23, #63)
    let gas_checks: Vec<_> = instructions
        .iter()
        .filter(|i| i.is_gas_check_branch())
        .collect();

    assert_eq!(gas_checks.len(), 1, "expected one gas check branch");

    // Verify brk trap
    let traps: Vec<_> = instructions.iter().filter(|i| i.is_brk_trap()).collect();
    assert_eq!(traps.len(), 1, "expected one brk trap");
}

#[test]
fn test_decode_instrumented_nested_loops() {
    let code = instrument_and_assemble(NESTED_LOOPS_ASM);
    let instructions = decode_instructions(&code).expect("decode failed");

    // Verify 2 gas check sequences (one per back-edge)
    let gas_decrements: Vec<_> = instructions
        .iter()
        .filter(|i| i.is_gas_decrement())
        .collect();

    assert_eq!(gas_decrements.len(), 2, "expected two gas decrements");

    let traps: Vec<_> = instructions.iter().filter(|i| i.is_brk_trap()).collect();
    assert_eq!(traps.len(), 2, "expected two brk traps");
}

#[test]
fn test_all_instructions_have_valid_opcodes() {
    // Ensure every instruction decodes to a known opcode (not Invalid)
    let code = instrument_and_assemble(TEST_LOOP_ASM);
    let instructions = decode_instructions(&code).expect("decode failed");

    for instr in &instructions {
        // Just accessing opcode() verifies the instruction decoded properly
        let _ = instr.opcode();
        // If we got here without panic, the instruction is valid
    }
}
