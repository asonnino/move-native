//! Gas instrumentation pass
//!
//! Inserts gas metering sequences at back-edges (loops) to enforce bounded execution.
//!
//! ## Gas Semantics for Nested Loops
//!
//! Each back-edge charges gas for instructions in its own basic block only.
//! Basic blocks are disjoint, so no instruction is ever charged twice.
//!
//! For nested loops like:
//! ```asm
//! .Louter:
//!     mov x1, #0
//! .Linner:
//!     add x1, x1, #1      ; inner block
//!     cmp x1, #10         ; inner block
//!     b.lt .Linner        ; inner back-edge charges 3 instructions
//!     add x0, x0, #1      ; outer block (after inner loop)
//!     cmp x0, #10         ; outer block
//!     b.lt .Louter        ; outer back-edge charges 3 instructions
//! ```
//!
//! The inner loop's gas check only charges for the 3 instructions in the inner block.
//! The outer loop's gas check only charges for the 3 instructions after the inner loop.
//! There is no double-charging because the inner loop instructions are in a separate
//! basic block from the outer loop's back-edge block.

use std::collections::HashMap;

use petgraph::graph::NodeIndex;

use crate::{
    cfg::{count_instructions, Cfg},
    parser::ParsedLine,
};

/// Gas counter register (per DeCl paper, x23 is callee-saved)
const GAS_REGISTER: &str = "x23";

/// Maximum immediate value for ARM64 sub instruction (12-bit)
const MAX_SUB_IMMEDIATE: usize = 4095;

/// Configuration for instrumentation
#[derive(Debug, Clone, Default)]
pub struct InstrumentConfig {
    /// Whether to emit .bundle_lock/.bundle_unlock directives
    /// These require LLVM's integrated assembler; Apple's as doesn't support them
    pub emit_bundle_directives: bool,
}

/// Instrument assembly with gas checks at back-edges
///
/// For each basic block that ends with a back-edge branch, inserts:
/// ```asm
/// .bundle_lock          // (optional, if config.emit_bundle_directives)
/// sub x23, x23, #N      // N = instructions in block
/// tbz x23, #63, .Lok_M  // if positive, continue
/// brk #0                // trap - out of gas
/// .Lok_M:
/// <original branch>
/// .bundle_unlock        // (optional, if config.emit_bundle_directives)
/// ```
pub fn instrument(lines: &[ParsedLine], cfg: &Cfg) -> String {
    instrument_with_config(lines, cfg, &InstrumentConfig::default())
}

/// Instrument assembly with gas checks at back-edges (with configuration)
pub fn instrument_with_config(
    lines: &[ParsedLine],
    cfg: &Cfg,
    config: &InstrumentConfig,
) -> String {
    let mut output = String::new();
    let mut gas_check_counter = 0;

    // Track which line indices have back-edge branches
    let mut back_edge_lines: HashMap<usize, NodeIndex> = HashMap::new();

    for block_idx in cfg.blocks() {
        let block = cfg.block(block_idx);
        if block.has_back_edge {
            // Find the line with the terminating branch
            if let Some(&branch_line_idx) = block.line_indices.iter().rev().find(|&&idx| {
                lines[idx]
                    .instruction
                    .as_ref()
                    .map(|i| i.is_branch())
                    .unwrap_or(false)
            }) {
                back_edge_lines.insert(branch_line_idx, block_idx);
            }
        }
    }

    // Generate output, inserting gas checks where needed
    for (idx, line) in lines.iter().enumerate() {
        if let Some(&block_idx) = back_edge_lines.get(&idx) {
            // This line has a back-edge branch - insert gas check before it
            let instruction_count = count_instructions(cfg, block_idx, lines);
            let label = format!(".Lok_{}", gas_check_counter);
            gas_check_counter += 1;

            // Emit leading whitespace/label from original line if any
            if let Some(ref lbl) = line.label {
                output.push_str(&format!("{}:\n", lbl));
            }

            // Emit bundle lock (optional)
            if config.emit_bundle_directives {
                output.push_str("    .bundle_lock\n");
            }

            // Emit gas decrement (may need multiple instructions for large counts)
            emit_gas_decrement(&mut output, instruction_count);
            output.push_str(&format!("    tbz {}, #63, {}\n", GAS_REGISTER, label));
            output.push_str("    brk #0\n");
            output.push_str(&format!("{}:\n", label));

            // Emit original branch instruction
            if let Some(ref instr) = line.instruction {
                output.push_str(&format!(
                    "    {} {}\n",
                    instr.mnemonic,
                    instr.operands.join(", ")
                ));
            }

            // Emit bundle unlock (optional)
            if config.emit_bundle_directives {
                output.push_str("    .bundle_unlock\n");
            }
        } else {
            // Regular line - emit as-is
            output.push_str(&line.original);
            output.push('\n');
        }
    }

    output
}

/// Emit gas decrement instruction(s) to the output
/// Handles large instruction counts by emitting multiple sub instructions
/// (ARM64 sub immediate is limited to 12 bits = 4095 max)
fn emit_gas_decrement(output: &mut String, mut count: usize) {
    while count > MAX_SUB_IMMEDIATE {
        output.push_str(&format!(
            "    sub {}, {}, #{}\n",
            GAS_REGISTER, GAS_REGISTER, MAX_SUB_IMMEDIATE
        ));
        count -= MAX_SUB_IMMEDIATE;
    }
    if count > 0 {
        output.push_str(&format!(
            "    sub {}, {}, #{}\n",
            GAS_REGISTER, GAS_REGISTER, count
        ));
    }
}

/// Generate gas decrement instructions as a vector of strings
/// Handles large instruction counts by emitting multiple sub instructions
fn gas_decrement_instructions(mut count: usize) -> Vec<String> {
    let mut instructions = Vec::new();
    while count > MAX_SUB_IMMEDIATE {
        instructions.push(format!(
            "    sub {}, {}, #{}",
            GAS_REGISTER, GAS_REGISTER, MAX_SUB_IMMEDIATE
        ));
        count -= MAX_SUB_IMMEDIATE;
    }
    if count > 0 {
        instructions.push(format!(
            "    sub {}, {}, #{}",
            GAS_REGISTER, GAS_REGISTER, count
        ));
    }
    instructions
}

/// Generate gas check instruction sequence as separate lines
pub fn gas_check_sequence(instr_count: usize, label: &str) -> Vec<String> {
    let mut result = vec!["    .bundle_lock".to_string()];
    result.extend(gas_decrement_instructions(instr_count));
    result.push(format!("    tbz {}, #63, {}", GAS_REGISTER, label));
    result.push("    brk #0".to_string());
    result.push(format!("{}:", label));
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{cfg::build, parser::Parser};

    #[test]
    fn test_instrument_simple_loop() {
        let input = r#".global _test_loop
.align 4

_test_loop:
    mov x0, #0
    mov x1, #1000000

.Lloop:
    add x0, x0, #1
    cmp x0, x1
    b.lt .Lloop

    ret
"#;
        let parser = Parser {};
        let lines = parser.parse(input).unwrap();
        let cfg = build(&lines);
        let output = instrument(&lines, &cfg);

        // Check that gas check was inserted (without bundle directives by default)
        assert!(output.contains("sub x23, x23, #"));
        assert!(output.contains("tbz x23, #63,"));
        assert!(output.contains("brk #0"));

        // Check that original branch is still there
        assert!(output.contains("b.lt .Lloop"));

        println!("Instrumented output:\n{}", output);
    }

    #[test]
    fn test_instrument_with_bundle_directives() {
        let input = r#".Lloop:
    add x0, x0, #1
    b .Lloop
"#;
        let parser = Parser {};
        let lines = parser.parse(input).unwrap();
        let cfg = build(&lines);
        let config = InstrumentConfig {
            emit_bundle_directives: true,
        };
        let output = instrument_with_config(&lines, &cfg, &config);

        // Check bundle directives are present
        assert!(output.contains(".bundle_lock"));
        assert!(output.contains(".bundle_unlock"));
    }

    #[test]
    fn test_no_instrumentation_without_loops() {
        let input = r#".global _simple
_simple:
    mov x0, #42
    ret
"#;
        let parser = Parser {};
        let lines = parser.parse(input).unwrap();
        let cfg = build(&lines);
        let output = instrument(&lines, &cfg);

        // Should not have gas checks
        assert!(!output.contains("sub x23"));
    }

    #[test]
    fn test_gas_decrement_small_count() {
        let mut output = String::new();
        super::emit_gas_decrement(&mut output, 100);
        assert_eq!(output, "    sub x23, x23, #100\n");
    }

    #[test]
    fn test_gas_decrement_max_immediate() {
        let mut output = String::new();
        super::emit_gas_decrement(&mut output, 4095);
        assert_eq!(output, "    sub x23, x23, #4095\n");
    }

    #[test]
    fn test_gas_decrement_large_count() {
        // Test count > 4095 requires multiple sub instructions
        let mut output = String::new();
        super::emit_gas_decrement(&mut output, 5000);

        // Should emit: sub x23, x23, #4095 followed by sub x23, x23, #905
        assert!(output.contains("sub x23, x23, #4095"));
        assert!(output.contains("sub x23, x23, #905"));

        // Count the number of sub instructions
        let sub_count = output.matches("sub x23").count();
        assert_eq!(sub_count, 2);
    }

    #[test]
    fn test_gas_decrement_very_large_count() {
        // Test count requiring 3+ sub instructions
        let mut output = String::new();
        super::emit_gas_decrement(&mut output, 10000);

        // 10000 = 4095 + 4095 + 1810
        let sub_count = output.matches("sub x23").count();
        assert_eq!(sub_count, 3);
        assert!(output.contains("sub x23, x23, #4095"));
        assert!(output.contains("sub x23, x23, #1810"));
    }

    #[test]
    fn test_gas_check_sequence_large_count() {
        let seq = super::gas_check_sequence(5000, ".Lok");

        // Should have bundle_lock, multiple subs, tbz, brk, label
        assert!(seq.iter().any(|s| s.contains(".bundle_lock")));
        assert!(seq.iter().any(|s| s.contains("sub x23, x23, #4095")));
        assert!(seq.iter().any(|s| s.contains("sub x23, x23, #905")));
        assert!(seq.iter().any(|s| s.contains("tbz x23, #63")));
        assert!(seq.iter().any(|s| s.contains("brk #0")));
    }

    #[test]
    fn test_nested_loop_no_double_charging() {
        // Verify that nested loops charge independently with no overlap
        // Inner loop: 3 instructions (add, cmp, b.lt)
        // Outer loop block after inner: 3 instructions (add, cmp, b.lt)
        let input = r#"
_nested:
    mov x0, #0
.Louter:
    mov x1, #0
.Linner:
    add x1, x1, #1
    cmp x1, #10
    b.lt .Linner
    add x0, x0, #1
    cmp x0, #10
    b.lt .Louter
    ret
"#;
        let parser = Parser {};
        let lines = parser.parse(input).unwrap();
        let cfg = build(&lines);
        let output = instrument(&lines, &cfg);

        // Should have exactly 2 gas checks (one per back-edge)
        let gas_check_count = output.matches("tbz x23, #63").count();
        assert_eq!(gas_check_count, 2, "Should have exactly 2 gas checks for nested loops");

        // Both should charge for 3 instructions (their own block only)
        // Count occurrences of "sub x23, x23, #3"
        let sub_3_count = output.matches("sub x23, x23, #3").count();
        assert_eq!(
            sub_3_count, 2,
            "Both loops should charge for 3 instructions each (no double-charging)"
        );

        // Verify both back-edges are instrumented
        assert!(output.contains("b.lt .Linner"), "Inner branch should be present");
        assert!(output.contains("b.lt .Louter"), "Outer branch should be present");
    }

    #[test]
    fn test_nested_loop_instruction_counts() {
        // More detailed test of instruction counting for nested loops
        use crate::cfg::count_instructions;

        let input = r#"
.Louter:
    mov x1, #0
.Linner:
    add x1, x1, #1
    nop
    nop
    cmp x1, #10
    b.lt .Linner
    add x0, x0, #1
    cmp x0, #10
    b.lt .Louter
    ret
"#;
        let parser = Parser {};
        let lines = parser.parse(input).unwrap();
        let cfg = build(&lines);

        // Find the blocks with back-edges and verify their instruction counts
        let mut inner_count = None;
        let mut outer_count = None;

        for block_idx in cfg.blocks() {
            let block = cfg.block(block_idx);
            if block.has_back_edge {
                let count = count_instructions(&cfg, block_idx, &lines);
                if block.back_edge_target == Some(".Linner".to_string()) {
                    inner_count = Some(count);
                } else if block.back_edge_target == Some(".Louter".to_string()) {
                    outer_count = Some(count);
                }
            }
        }

        // Inner block: add, nop, nop, cmp, b.lt = 5 instructions
        assert_eq!(inner_count, Some(5), "Inner loop block should have 5 instructions");

        // Outer block (after inner): add, cmp, b.lt = 3 instructions
        assert_eq!(outer_count, Some(3), "Outer loop block should have 3 instructions");

        // Total instructions charged per full iteration: 5 (inner) + 3 (outer) = 8
        // NOT 5 + 5 + 3 = 13 (which would be double-charging)
    }
}
