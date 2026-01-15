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

use std::collections::{HashMap, HashSet};

use petgraph::graph::NodeIndex;

use crate::{cfg::Cfg, parser::ParsedLine};

/// Gas counter register (per DeCl paper, x23 is callee-saved)
const GAS_REGISTER: &str = "x23";

/// Maximum immediate value for ARM64 sub instruction (12-bit)
const MAX_SUB_IMMEDIATE: usize = 4095;

/// Prefix for generated gas check labels (uses double underscore to indicate internal/generated)
const GAS_LABEL_PREFIX: &str = ".L__gas_ok_";

/// Instrument assembly with gas checks at back-edges
///
/// For each basic block that ends with a back-edge branch, inserts:
/// ```asm
/// sub x23, x23, #N      // N = instructions in block
/// tbz x23, #63, .Lok_M  // if positive, continue
/// brk #0                // trap - out of gas
/// .Lok_M:
/// <original branch>
/// ```
pub fn instrument(lines: &[ParsedLine], cfg: &Cfg) -> String {
    Instrumenter::new(lines, cfg).run()
}

/// State for instrumenting assembly with gas checks
struct Instrumenter<'a> {
    lines: &'a [ParsedLine],
    cfg: &'a Cfg,
    existing_labels: HashSet<String>,
    label_counter: usize,
    output: String,
}

impl<'a> Instrumenter<'a> {
    /// Creates a new instrumenter, collecting existing labels to avoid collisions.
    fn new(lines: &'a [ParsedLine], cfg: &'a Cfg) -> Self {
        let existing_labels = lines.iter().filter_map(|line| line.label.clone()).collect();
        Self {
            lines,
            cfg,
            existing_labels,
            label_counter: 0,
            output: String::new(),
        }
    }

    /// Processes all lines, inserting gas checks at back-edges.
    fn run(mut self) -> String {
        let back_edge_lines = self.find_back_edge_lines();

        for (idx, line) in self.lines.iter().enumerate() {
            if let Some(&block_idx) = back_edge_lines.get(&idx) {
                self.emit_instrumented_line(line, block_idx);
            } else {
                self.emit_original_line(line);
            }
        }

        self.output
    }

    /// Maps line indices to block indices for lines containing back-edge branches.
    fn find_back_edge_lines(&self) -> HashMap<usize, NodeIndex> {
        let mut back_edge_lines = HashMap::new();

        for block_idx in self.cfg.blocks() {
            if self.cfg.has_back_edge(block_idx) {
                let block = self.cfg.block(block_idx);
                if let Some(branch_line_idx) = block.line_indices.clone().rev().find(|&idx| {
                    self.lines[idx]
                        .instruction
                        .as_ref()
                        .map(|i| i.is_branch())
                        .unwrap_or(false)
                }) {
                    back_edge_lines.insert(branch_line_idx, block_idx);
                }
            }
        }

        back_edge_lines
    }

    /// Emits gas check sequence followed by the original branch instruction.
    fn emit_instrumented_line(&mut self, line: &ParsedLine, block_idx: NodeIndex) {
        let instruction_count = self.cfg.count_instructions(block_idx, self.lines);
        let label = self.generate_unique_label();

        if let Some(ref lbl) = line.label {
            self.output.push_str(&format!("{}:\n", lbl));
        }

        self.emit_gas_decrement(instruction_count);
        self.output
            .push_str(&format!("    tbz {}, #63, {}\n", GAS_REGISTER, label));
        self.output.push_str("    brk #0\n");
        self.output.push_str(&format!("{}:\n", label));

        if let Some(ref instr) = line.instruction {
            self.output.push_str(&format!(
                "    {} {}\n",
                instr.mnemonic,
                instr.operands.join(", ")
            ));
        }
    }

    /// Emits a line unchanged (no gas check needed).
    fn emit_original_line(&mut self, line: &ParsedLine) {
        self.output.push_str(&line.original);
        self.output.push('\n');
    }

    /// Generates a unique label, skipping any that collide with existing labels.
    fn generate_unique_label(&mut self) -> String {
        loop {
            let label = format!("{}{}", GAS_LABEL_PREFIX, self.label_counter);
            self.label_counter += 1;

            if !self.existing_labels.contains(&label) {
                return label;
            }
        }
    }

    /// Emits sub instruction(s) to decrement gas counter (splits if count > 4095).
    fn emit_gas_decrement(&mut self, mut count: usize) {
        while count > MAX_SUB_IMMEDIATE {
            self.output.push_str(&format!(
                "    sub {}, {}, #{}\n",
                GAS_REGISTER, GAS_REGISTER, MAX_SUB_IMMEDIATE
            ));
            count -= MAX_SUB_IMMEDIATE;
        }
        if count > 0 {
            self.output.push_str(&format!(
                "    sub {}, {}, #{}\n",
                GAS_REGISTER, GAS_REGISTER, count
            ));
        }
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
    let mut result = gas_decrement_instructions(instr_count);
    result.push(format!("    tbz {}, #63, {}", GAS_REGISTER, label));
    result.push("    brk #0".to_string());
    result.push(format!("{}:", label));
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{cfg::Cfg, parser::Parser};

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
        let cfg = Cfg::from_lines(&lines);
        let output = instrument(&lines, &cfg);

        // Check that gas check was inserted
        assert!(output.contains("sub x23, x23, #"));
        assert!(output.contains("tbz x23, #63,"));
        assert!(output.contains("brk #0"));

        // Check that original branch is still there
        assert!(output.contains("b.lt .Lloop"));

        println!("Instrumented output:\n{}", output);
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
        let cfg = Cfg::from_lines(&lines);
        let output = instrument(&lines, &cfg);

        // Should not have gas checks
        assert!(!output.contains("sub x23"));
    }

    #[test]
    fn test_gas_decrement_small_count() {
        let instrs = gas_decrement_instructions(100);
        assert_eq!(instrs.len(), 1);
        assert_eq!(instrs[0], "    sub x23, x23, #100");
    }

    #[test]
    fn test_gas_decrement_max_immediate() {
        let instrs = gas_decrement_instructions(4095);
        assert_eq!(instrs.len(), 1);
        assert_eq!(instrs[0], "    sub x23, x23, #4095");
    }

    #[test]
    fn test_gas_decrement_large_count() {
        // Test count > 4095 requires multiple sub instructions
        let instrs = gas_decrement_instructions(5000);

        // Should emit: sub x23, x23, #4095 followed by sub x23, x23, #905
        assert_eq!(instrs.len(), 2);
        assert!(instrs[0].contains("sub x23, x23, #4095"));
        assert!(instrs[1].contains("sub x23, x23, #905"));
    }

    #[test]
    fn test_gas_decrement_very_large_count() {
        // Test count requiring 3+ sub instructions
        let instrs = gas_decrement_instructions(10000);

        // 10000 = 4095 + 4095 + 1810
        assert_eq!(instrs.len(), 3);
        assert!(instrs[0].contains("sub x23, x23, #4095"));
        assert!(instrs[1].contains("sub x23, x23, #4095"));
        assert!(instrs[2].contains("sub x23, x23, #1810"));
    }

    #[test]
    fn test_gas_check_sequence_large_count() {
        let seq = super::gas_check_sequence(5000, ".Lok");

        // Should have multiple subs, tbz, brk, label
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
        let cfg = Cfg::from_lines(&lines);
        let output = instrument(&lines, &cfg);

        // Should have exactly 2 gas checks (one per back-edge)
        let gas_check_count = output.matches("tbz x23, #63").count();
        assert_eq!(
            gas_check_count, 2,
            "Should have exactly 2 gas checks for nested loops"
        );

        // Both should charge for 3 instructions (their own block only)
        // Count occurrences of "sub x23, x23, #3"
        let sub_3_count = output.matches("sub x23, x23, #3").count();
        assert_eq!(
            sub_3_count, 2,
            "Both loops should charge for 3 instructions each (no double-charging)"
        );

        // Verify both back-edges are instrumented
        assert!(
            output.contains("b.lt .Linner"),
            "Inner branch should be present"
        );
        assert!(
            output.contains("b.lt .Louter"),
            "Outer branch should be present"
        );
    }

    #[test]
    fn test_nested_loop_instruction_counts() {
        // More detailed test of instruction counting for nested loops

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
        let cfg = Cfg::from_lines(&lines);

        // Find the blocks with back-edges and verify their instruction counts
        let mut inner_count = None;
        let mut outer_count = None;

        for block_idx in cfg.blocks() {
            if cfg.has_back_edge(block_idx) {
                let count = cfg.count_instructions(block_idx, &lines);
                if cfg.back_edge_target_label(block_idx) == Some(".Linner") {
                    inner_count = Some(count);
                } else if cfg.back_edge_target_label(block_idx) == Some(".Louter") {
                    outer_count = Some(count);
                }
            }
        }

        // Inner block: add, nop, nop, cmp, b.lt = 5 instructions
        assert_eq!(
            inner_count,
            Some(5),
            "Inner loop block should have 5 instructions"
        );

        // Outer block (after inner): add, cmp, b.lt = 3 instructions
        assert_eq!(
            outer_count,
            Some(3),
            "Outer loop block should have 3 instructions"
        );

        // Total instructions charged per full iteration: 5 (inner) + 3 (outer) = 8
        // NOT 5 + 5 + 3 = 13 (which would be double-charging)
    }

    #[test]
    fn test_label_uses_unique_prefix() {
        // Verify that generated labels use the unique prefix
        let input = r#"
.Lloop:
    add x0, x0, #1
    b .Lloop
"#;
        let parser = Parser {};
        let lines = parser.parse(input).unwrap();
        let cfg = Cfg::from_lines(&lines);
        let output = instrument(&lines, &cfg);

        // Should use the unique prefix, not the old .Lok_ prefix
        assert!(
            output.contains(".L__gas_ok_"),
            "Should use unique .L__gas_ok_ prefix"
        );
        assert!(!output.contains(".Lok_"), "Should not use old .Lok_ prefix");
    }

    #[test]
    fn test_label_collision_avoidance() {
        // Input has labels that would collide with generated labels
        // The instrumenter should skip those and use the next available
        let input = r#"
.L__gas_ok_0:
    nop
.L__gas_ok_1:
    nop
.Lloop:
    add x0, x0, #1
    b .Lloop
"#;
        let parser = Parser {};
        let lines = parser.parse(input).unwrap();
        let cfg = Cfg::from_lines(&lines);
        let output = instrument(&lines, &cfg);

        // The generated label should skip 0 and 1 (which exist) and use 2
        assert!(
            output.contains(".L__gas_ok_2"),
            "Should skip colliding labels and use .L__gas_ok_2"
        );

        // Original labels should still be present
        assert!(output.contains(".L__gas_ok_0:"));
        assert!(output.contains(".L__gas_ok_1:"));
    }
}
