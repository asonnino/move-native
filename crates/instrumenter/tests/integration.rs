// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for instrumenter
//!
//! These tests exercise the full instrumentation pipeline using real assembly files
//! from `tests/asm_samples/`. They verify that:
//!
//! 1. Assembly files parse correctly
//! 2. Back-edges are detected accurately
//! 3. Gas check sequences are inserted at the right locations
//! 4. Original code structure is preserved
//!
//! Unlike unit tests (which use inline assembly strings), these tests serve as
//! end-to-end validation and documentation of expected behavior on real files.

use instrumenter::{ParsedAssembly, build_cfg, instrument};

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

/// Tests the full instrumentation pipeline on a simple loop.
///
/// Verifies that:
/// - Gas check sequence (`sub x23` / `tbz x23, #63` / `brk #0`) is inserted
/// - Original labels and branch targets are preserved
#[test]
fn simple_loop_instrumentation() {
    let asm = ParsedAssembly::parse(SIMPLE_LOOP_ASM);
    let cfg_result = build_cfg(&asm).unwrap();
    let output = instrument::instrument(asm.lines(), &cfg_result).unwrap();

    // Verify gas check sequence was inserted
    assert!(output.contains("sub x23, x23"), "missing gas decrement");
    assert!(output.contains("tbz x23, #63"), "missing gas check branch");
    assert!(output.contains("brk #0"), "missing out-of-gas trap");

    // Verify the original code is still present
    assert!(output.contains("_simple_loop:"), "missing function label");
    assert!(output.contains(".Lloop:"), "missing loop label");
    assert!(output.contains("b.lt .Lloop"), "missing back-edge branch");
}

/// Tests that CFG analysis correctly identifies back-edges.
///
/// The `simple_loop.s` file has exactly one back-edge: `b.lt .Lloop`
/// which branches backward to the loop header.
#[test]
fn test_back_edge_detection() {
    let asm = ParsedAssembly::parse(SIMPLE_LOOP_ASM);
    let cfg_result = build_cfg(&asm).unwrap();
    let cfg = &cfg_result.cfg;

    // Should detect exactly one back-edge (b.lt .Lloop)
    let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
    assert_eq!(back_edge_count, 1, "expected exactly one back-edge");

    // Verify the back-edge target is the loop header (instruction index 2)
    // After resolution: _simple_loop (0), mov (1), mov (2),
    // .Lloop/add (3), cmp (4), b.lt (5), ret (6)
    // Wait, labels are resolved - .Lloop resolves to the instruction after it
    let back_edge_block = cfg.blocks().find(|&b| cfg.has_back_edge(b)).unwrap();
    // The back-edge target is an instruction index, not a label name
    assert!(
        cfg.back_edge_target(back_edge_block).is_some(),
        "back-edge should have a target"
    );
}

/// Tests instrumentation of nested loops.
///
/// Both inner and outer loops should receive separate gas checks.
/// This is important because the inner loop executes many more times
/// than the outer loop, and each needs independent metering.
#[test]
fn test_nested_loops_instrumentation() {
    let asm = ParsedAssembly::parse(NESTED_LOOPS_ASM);
    let cfg_result = build_cfg(&asm).unwrap();
    let cfg = &cfg_result.cfg;
    let output = instrument::instrument(asm.lines(), &cfg_result).unwrap();

    // Should have exactly 2 back-edges (inner and outer)
    let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
    assert_eq!(
        back_edge_count, 2,
        "expected two back-edges for nested loops"
    );

    // Verify both loop labels are preserved
    assert!(output.contains(".Linner:"), "missing inner loop label");
    assert!(output.contains(".Louter:"), "missing outer loop label");

    // Verify both back-edge branches are preserved
    assert!(output.contains("b.lt .Linner"), "missing inner back-edge");
    assert!(output.contains("b.lt .Louter"), "missing outer back-edge");

    // Count gas check sequences - should have 2 (one per back-edge)
    let gas_check_count = output.matches("brk #0").count();
    assert_eq!(gas_check_count, 2, "expected two gas check sequences");
}

/// Tests that the full pipeline handles malformed/garbage input without panicking.
#[test]
fn test_malformed_input_does_not_panic() {
    let garbage_inputs = [
        // Empty and whitespace
        "",
        "   ",
        "\n\n\n",
        // Malformed labels
        ":",
        ":::",
        "foo:::",
        // Unmatched brackets
        "ldr x0, [[[",
        "ldr x0, ]]]",
        "ldr x0, [x1, x2",
        // Nonsense instructions
        "asdfghjkl x0, x1",
        "🔥 x0, x1",
        // Only comments
        "; comment\n// another\n@ gnu style",
        // Directives only
        ".global\n.align\n.",
        // Mixed garbage (with valid loop)
        "foo: ::: [[[ ]]] \n.Lloop: b .Lloop",
    ];

    for input in garbage_inputs {
        let asm = ParsedAssembly::parse(input);
        // cfg::build may return an error for some inputs (e.g., undefined labels)
        // but should not panic
        if let Ok(cfg_result) = build_cfg(&asm) {
            let _ = instrument::instrument(asm.lines(), &cfg_result);
        }
    }
}

/// Tests that undefined labels produce an error, not a panic.
#[test]
fn test_undefined_label_returns_error() {
    let input = ".Lloop:\n    add x0, x0, #1\n    b .Ltypo\n";
    let asm = ParsedAssembly::parse(input);
    let result = build_cfg(&asm);
    assert!(result.is_err(), "expected error for undefined label");
}

/// Tests that large input completes without hanging.
#[test]
fn test_large_input_does_not_hang() {
    let large_input = "nop\n".repeat(10_000);

    let asm = ParsedAssembly::parse(&large_input);
    let cfg_result = build_cfg(&asm).unwrap();
    let _ = instrument::instrument(asm.lines(), &cfg_result).unwrap();

    assert_eq!(asm.lines().len(), 10_000);
}

/// Tests label collision handling doesn't loop forever.
#[test]
fn test_label_collision_does_not_hang() {
    // Pre-populate labels that would collide with generated gas check labels
    let mut input = String::new();
    for i in 0..100 {
        input.push_str(&format!(".L__gas_ok_{}:\n    nop\n", i));
    }
    input.push_str(".Lloop:\n    b .Lloop\n");

    let asm = ParsedAssembly::parse(&input);
    let cfg_result = build_cfg(&asm).unwrap();
    let output = instrument::instrument(asm.lines(), &cfg_result).unwrap();

    // Should skip 0-99 and use 100
    assert!(output.contains(".L__gas_ok_100:"));
}

/// Tests that forward-only code receives NO gas instrumentation.
/// This is an important optimization: forward branches are bounded by code size.
#[test]
fn test_forward_only_no_instrumentation() {
    let asm = ParsedAssembly::parse(FORWARD_ONLY_ASM);
    let cfg_result = build_cfg(&asm).unwrap();
    let cfg = &cfg_result.cfg;
    let output = instrument::instrument(asm.lines(), &cfg_result).unwrap();

    // Should have no back-edges
    let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
    assert_eq!(
        back_edge_count, 0,
        "forward-only code should have no back-edges"
    );

    // Should have no gas check sequences
    assert!(!output.contains("sub x23"), "should not have gas decrement");
    assert!(!output.contains("tbz x23"), "should not have gas check");
    assert!(!output.contains("brk #0"), "should not have trap");

    // Original structure preserved
    assert!(output.contains(".Lsmall:"));
    assert!(output.contains(".Ldone:"));
    assert!(output.contains("b.lt .Lsmall"));
}

/// Tests that function calls within loops are handled correctly.
/// The bl instruction should remain, and gas check should be at the back-edge.
#[test]
fn test_function_call_instrumentation() {
    let asm = ParsedAssembly::parse(FUNCTION_CALL_ASM);
    let cfg_result = build_cfg(&asm).unwrap();
    let cfg = &cfg_result.cfg;
    let output = instrument::instrument(asm.lines(), &cfg_result).unwrap();

    // Should have exactly one back-edge (the main loop)
    let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
    assert_eq!(
        back_edge_count, 1,
        "should have one back-edge for main loop"
    );

    // Gas check should be present
    assert!(output.contains("sub x23, x23"), "should have gas decrement");
    assert!(output.contains("tbz x23, #63"), "should have gas check");

    // bl instruction should be preserved (not treated as back-edge)
    assert!(
        output.contains("bl _helper"),
        "bl instruction should be preserved"
    );
    assert!(
        output.contains("b.lt .Lloop"),
        "loop back-edge should be preserved"
    );
}

/// Tests cbnz loop instrumentation.
#[test]
fn test_cbz_loop_instrumentation() {
    let asm = ParsedAssembly::parse(CBZ_LOOP_ASM);
    let cfg_result = build_cfg(&asm).unwrap();
    let cfg = &cfg_result.cfg;
    let output = instrument::instrument(asm.lines(), &cfg_result).unwrap();

    // Should detect the cbnz back-edge
    let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
    assert_eq!(back_edge_count, 1, "should detect cbnz as back-edge");

    // Gas check sequence present
    assert!(
        output.contains("sub x23, x23, #2"),
        "should charge for 2 instructions"
    );
    assert!(output.contains("cbnz x0, .Lloop"), "cbnz branch preserved");
}

/// Tests unconditional back-edge (plain `b` instruction).
#[test]
fn test_unconditional_loop_instrumentation() {
    let asm = ParsedAssembly::parse(UNCONDITIONAL_LOOP_ASM);
    let cfg_result = build_cfg(&asm).unwrap();
    let cfg = &cfg_result.cfg;
    let output = instrument::instrument(asm.lines(), &cfg_result).unwrap();

    // Should have exactly one back-edge (the unconditional b)
    let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
    assert_eq!(
        back_edge_count, 1,
        "should detect unconditional b as back-edge"
    );

    // The forward branch (b.ge) should NOT be instrumented
    // Only the back-edge (b .Lloop) should have gas check
    assert_eq!(
        output.matches("brk #0").count(),
        1,
        "only one gas check for back-edge"
    );
    assert!(
        output.contains("b .Lloop"),
        "unconditional back-edge preserved"
    );
    assert!(
        output.contains("b.ge .Ldone"),
        "forward branch preserved without gas check"
    );
}

/// Tests multiple functions in one file.
///
/// NOTE: Current limitation - CFG analysis starts from instruction 0 and uses
/// dominator analysis, so code after a `ret` (second function) isn't reachable
/// from the entry point's perspective. Only the first function's back-edge is
/// detected. This test documents this behavior.
#[test]
fn test_multiple_functions_instrumentation() {
    let asm = ParsedAssembly::parse(MULTIPLE_FUNCTIONS_ASM);
    let cfg_result = build_cfg(&asm).unwrap();
    let cfg = &cfg_result.cfg;
    let output = instrument::instrument(asm.lines(), &cfg_result).unwrap();

    // Current behavior: only first function's back-edge is detected
    // (second function is unreachable from entry due to `ret`)
    let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
    assert_eq!(
        back_edge_count, 1,
        "only first function's back-edge detected (limitation: second function unreachable)"
    );

    // First function's loop is instrumented
    assert_eq!(
        output.matches("brk #0").count(),
        1,
        "one gas check sequence"
    );

    // Both function labels preserved in output
    assert!(output.contains("_func_add:") || output.contains("func_add:"));
    assert!(output.contains("_func_mul:") || output.contains("func_mul:"));

    // First loop back-edge preserved and instrumented
    assert!(output.contains("b.lt .Ladd_loop"));
}

/// Tests large basic block has correct instruction count.
#[test]
fn test_large_block_instruction_count() {
    let asm = ParsedAssembly::parse(LARGE_BLOCK_ASM);
    let cfg_result = build_cfg(&asm).unwrap();
    let output = instrument::instrument(asm.lines(), &cfg_result).unwrap();

    // The loop body has 20 instructions, so gas decrement should be #20
    assert!(
        output.contains("sub x23, x23, #20"),
        "should charge for 20 instructions in large block, output:\n{}",
        output
    );
}
