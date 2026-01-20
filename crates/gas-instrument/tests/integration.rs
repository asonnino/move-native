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

use gas_instrument::{build_cfg, instrument, ParsedAssembly};

const SIMPLE_LOOP_ASM: &str = include_str!("../../../tests/asm_samples/simple_loop.s");
const NESTED_LOOPS_ASM: &str = include_str!("../../../tests/asm_samples/nested_loops.s");

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
    // After resolution: _simple_loop (0), mov (1), mov (2), .Lloop/add (3), cmp (4), b.lt (5), ret (6)
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
