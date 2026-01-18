//! Integration tests for gas-instrument
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

use gas_instrument::{cfg, instrument, parser};

const TEST_LOOP_ASM: &str = include_str!("../../../tests/asm_samples/test_loop.s");
const NESTED_LOOPS_ASM: &str = include_str!("../../../tests/asm_samples/nested_loops.s");

/// Tests the full instrumentation pipeline on a simple loop.
///
/// Verifies that:
/// - Gas check sequence (`sub x23` / `tbz x23, #63` / `brk #0`) is inserted
/// - Original labels and branch targets are preserved
#[test]
fn test_loop_instrumentation() {
    let lines = parser::parse(TEST_LOOP_ASM);
    let cfg = cfg::build(&lines);
    let output = instrument::instrument(&lines, &cfg);

    // Verify gas check sequence was inserted
    assert!(output.contains("sub x23, x23"), "missing gas decrement");
    assert!(output.contains("tbz x23, #63"), "missing gas check branch");
    assert!(output.contains("brk #0"), "missing out-of-gas trap");

    // Verify the original code is still present
    assert!(output.contains("_test_loop:"), "missing function label");
    assert!(output.contains(".Lloop:"), "missing loop label");
    assert!(output.contains("b.lt .Lloop"), "missing back-edge branch");
}

/// Tests that CFG analysis correctly identifies back-edges.
///
/// The `test_loop.s` file has exactly one back-edge: `b.lt .Lloop`
/// which branches backward to the loop header.
#[test]
fn test_back_edge_detection() {
    let lines = parser::parse(TEST_LOOP_ASM);
    let cfg = cfg::build(&lines);

    // Should detect exactly one back-edge (b.lt .Lloop)
    let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
    assert_eq!(back_edge_count, 1, "expected exactly one back-edge");

    // Verify the back-edge target is .Lloop
    let back_edge_block = cfg.blocks().find(|&b| cfg.has_back_edge(b)).unwrap();
    assert_eq!(
        cfg.back_edge_target(back_edge_block).map(|s| s.as_str()),
        Some(".Lloop"),
        "back-edge should target .Lloop"
    );
}

/// Tests instrumentation of nested loops.
///
/// Both inner and outer loops should receive separate gas checks.
/// This is important because the inner loop executes many more times
/// than the outer loop, and each needs independent metering.
#[test]
fn test_nested_loops_instrumentation() {
    let lines = parser::parse(NESTED_LOOPS_ASM);
    let cfg = cfg::build(&lines);
    let output = instrument::instrument(&lines, &cfg);

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
        // Branch to non-existent label
        ".Lloop:\n    add x0, x0, #1\n    b .Ltypo\n",
        // Only comments
        "; comment\n// another\n@ gnu style",
        // Directives only
        ".global\n.align\n.",
        // Mixed garbage
        "foo: ::: [[[ ]]] \n.Lloop: b .Lloop",
    ];

    for input in garbage_inputs {
        let lines = parser::parse(input);
        let cfg = cfg::build(&lines);
        let _ = instrument::instrument(&lines, &cfg);
    }
}

/// Tests that large input completes without hanging.
#[test]
fn test_large_input_does_not_hang() {
    let large_input = "nop\n".repeat(10_000);

    let lines = parser::parse(&large_input);
    let cfg = cfg::build(&lines);
    let _ = instrument::instrument(&lines, &cfg);

    assert_eq!(lines.len(), 10_000);
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

    let lines = parser::parse(&input);
    let cfg = cfg::build(&lines);
    let output = instrument::instrument(&lines, &cfg);

    // Should skip 0-99 and use 100
    assert!(output.contains(".L__gas_ok_100:"));
}
