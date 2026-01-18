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

use crate::{
    parser::{ParsedLine, ResolvedInstruction, Statement},
    CfgResult,
    NodeIndex,
};

/// Errors that can occur during instrumentation
#[derive(Debug, thiserror::Error)]
pub enum InstrumentError {
    #[error("terminator index {index} exceeds resolved instructions ({count})")]
    InvalidTerminatorIndex { index: usize, count: usize },

    #[error("back-edge at line {line} is not an instruction")]
    NonInstructionBackEdge { line: usize },

    #[error("exceeded maximum label generation attempts ({max})")]
    LabelGenerationExhausted { max: usize },
}

/// Gas counter register (per DeCl paper, x23 is callee-saved)
const GAS_REGISTER: &str = "x23";

/// Maximum immediate value for ARM64 sub instruction (12-bit)
const MAX_SUB_IMMEDIATE: usize = 4095;

/// Prefix for generated gas check labels (uses double underscore to indicate internal/generated)
const GAS_LABEL_PREFIX: &str = ".L__gas_ok_";

/// Maximum attempts for generating a unique label before giving up
const MAX_LABEL_ATTEMPTS: usize = 10_000;

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
///
/// # Errors
///
/// Returns an error if:
/// - A terminator index is out of bounds
/// - A back-edge instruction is not actually an instruction
/// - Label generation exhausts all attempts (>10,000 collisions)
pub fn instrument(
    lines: &[ParsedLine<'_>],
    cfg_result: &CfgResult,
) -> Result<String, InstrumentError> {
    Instrumenter::new(lines, cfg_result).run()
}

/// State for instrumenting assembly with gas checks
struct Instrumenter<'a> {
    lines: &'a [ParsedLine<'a>],
    cfg: &'a cfg::Cfg,
    resolved: &'a [ResolvedInstruction],
    existing_labels: HashSet<String>,
    label_counter: usize,
    output: String,
}

impl<'a> Instrumenter<'a> {
    /// Creates a new instrumenter, collecting existing labels to avoid collisions.
    fn new(lines: &'a [ParsedLine<'a>], cfg_result: &'a CfgResult) -> Self {
        let existing_labels = lines
            .iter()
            .filter_map(|line| line.label.map(|s| s.to_string()))
            .collect();

        Self {
            lines,
            cfg: &cfg_result.cfg,
            resolved: &cfg_result.resolved,
            existing_labels,
            label_counter: 0,
            output: String::new(),
        }
    }

    /// Processes all lines, inserting gas checks at back-edges.
    fn run(mut self) -> Result<String, InstrumentError> {
        let back_edge_lines = self.find_back_edge_lines()?;

        for (idx, line) in self.lines.iter().enumerate() {
            // Line indices are 0-based, line_number is 1-based
            let line_number = idx + 1;
            if let Some(&block_idx) = back_edge_lines.get(&line_number) {
                self.emit_instrumented_line(line, block_idx, line_number)?;
            } else {
                self.emit_original_line(line);
            }
        }

        Ok(self.output)
    }

    /// Maps line numbers (1-indexed) to block indices for lines containing back-edge branches.
    fn find_back_edge_lines(&self) -> Result<HashMap<usize, NodeIndex>, InstrumentError> {
        let mut back_edge_lines = HashMap::new();

        for block_idx in self.cfg.blocks() {
            if self.cfg.has_back_edge(block_idx) {
                if let Some(terminator_idx) = self.cfg.terminator_index(block_idx) {
                    // terminator_idx is an instruction index in the resolved stream
                    // Map it back to the original line number
                    let resolved = self.resolved.get(terminator_idx).ok_or(
                        InstrumentError::InvalidTerminatorIndex {
                            index: terminator_idx,
                            count: self.resolved.len(),
                        },
                    )?;
                    back_edge_lines.insert(resolved.line_number, block_idx);
                }
            }
        }

        Ok(back_edge_lines)
    }

    /// Emits gas check sequence followed by the original branch instruction.
    fn emit_instrumented_line(
        &mut self,
        line: &ParsedLine,
        block_idx: NodeIndex,
        line_number: usize,
    ) -> Result<(), InstrumentError> {
        let instruction_count = self.cfg.instruction_count(block_idx);
        let label = self.generate_unique_label()?;

        // Preserve any label on the original line
        if let Some(ref lbl) = line.label {
            self.output.push_str(&format!("{}:\n", lbl));
        }

        // Gas check sequence:
        // 1. Decrement gas counter by number of instructions in this block
        self.emit_gas_decrement(instruction_count);
        // 2. Test bit 63 (sign bit): if 0 (positive), branch over trap
        self.output
            .push_str(&format!("    tbz {}, #63, {}\n", GAS_REGISTER, label));
        // 3. Trap if gas went negative (bit 63 = 1)
        self.output.push_str("    brk #0\n");
        // 4. Continue label
        self.output.push_str(&format!("{}:\n", label));

        // Emit the original back-edge branch instruction
        let Statement::Instruction(ref instruction) = line.statement else {
            return Err(InstrumentError::NonInstructionBackEdge { line: line_number });
        };
        self.output.push_str(&format!(
            "    {} {}\n",
            instruction.mnemonic,
            instruction.operands.join(", ")
        ));

        Ok(())
    }

    /// Emits a line unchanged (no gas check needed).
    fn emit_original_line(&mut self, line: &ParsedLine) {
        self.output.push_str(line.original);
        self.output.push('\n');
    }

    /// Generates a unique label, skipping any that collide with existing labels.
    fn generate_unique_label(&mut self) -> Result<String, InstrumentError> {
        for _ in 0..MAX_LABEL_ATTEMPTS {
            let label = format!("{}{}", GAS_LABEL_PREFIX, self.label_counter);
            self.label_counter += 1;

            if !self.existing_labels.contains(&label) {
                return Ok(label);
            }
        }
        Err(InstrumentError::LabelGenerationExhausted {
            max: MAX_LABEL_ATTEMPTS,
        })
    }

    /// Emits sub instruction(s) to decrement gas counter (splits if count > 4095).
    fn emit_gas_decrement(&mut self, count: usize) {
        for instruction in Self::gas_decrement_instructions(count) {
            self.output.push_str(&instruction);
            self.output.push('\n');
        }
    }

    /// Generate gas decrement instructions as a vector of strings.
    /// Handles large instruction counts by emitting multiple sub instructions.
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
}

#[cfg(test)]
mod tests {
    use indoc::indoc;

    use super::InstrumentError;
    use crate::{build_cfg, instrument::Instrumenter, CfgResult, ParsedAssembly};

    /// Helper to reduce test boilerplate: parses assembly and builds CFG
    fn parse_and_build(input: &str) -> (CfgResult, ParsedAssembly) {
        let asm = ParsedAssembly::parse(input);
        let cfg_result = build_cfg(&asm).unwrap();
        (cfg_result, asm)
    }

    #[test]
    fn test_instrument_simple_loop() {
        let (cfg_result, asm) = parse_and_build(indoc! {"
            .global _test_loop
            .align 4

            _test_loop:
                mov x0, #0
                mov x1, #1000000

            .Lloop:
                add x0, x0, #1
                cmp x0, x1
                b.lt .Lloop

                ret
        "});
        let output = crate::instrument(asm.lines(), &cfg_result).unwrap();

        assert!(output.contains("sub x23, x23, #"));
        assert!(output.contains("tbz x23, #63,"));
        assert!(output.contains("brk #0"));
        assert!(output.contains("b.lt .Lloop"));
    }

    #[test]
    fn test_no_instrumentation_without_loops() {
        let (cfg_result, asm) = parse_and_build(indoc! {"
            .global _simple
            _simple:
                mov x0, #42
                ret
        "});
        let output = crate::instrument(asm.lines(), &cfg_result).unwrap();

        assert!(!output.contains("sub x23"));
    }

    #[test]
    fn test_gas_decrement_small_count() {
        let instrumenter = Instrumenter::gas_decrement_instructions(100);
        assert_eq!(instrumenter.len(), 1);
        assert_eq!(instrumenter[0], "    sub x23, x23, #100");
    }

    #[test]
    fn test_gas_decrement_max_immediate() {
        let instrumenter = Instrumenter::gas_decrement_instructions(4095);
        assert_eq!(instrumenter.len(), 1);
        assert_eq!(instrumenter[0], "    sub x23, x23, #4095");
    }

    #[test]
    fn test_gas_decrement_large_count() {
        let instrumenter = Instrumenter::gas_decrement_instructions(5000);
        // 5000 = 4095 + 905
        assert_eq!(instrumenter.len(), 2);
        assert_eq!(instrumenter[0], "    sub x23, x23, #4095");
        assert_eq!(instrumenter[1], "    sub x23, x23, #905");
    }

    #[test]
    fn test_gas_decrement_very_large_count() {
        let instrumenter = Instrumenter::gas_decrement_instructions(10000);
        // 10000 = 4095 + 4095 + 1810
        assert_eq!(instrumenter.len(), 3);
        assert_eq!(instrumenter[0], "    sub x23, x23, #4095");
        assert_eq!(instrumenter[1], "    sub x23, x23, #4095");
        assert_eq!(instrumenter[2], "    sub x23, x23, #1810");
    }

    #[test]
    fn test_nested_loop_no_double_charging() {
        // Inner loop: 3 instructions (add, cmp, b.lt)
        // Outer loop: 3 instructions (add, cmp, b.lt)
        let (cfg_result, asm) = parse_and_build(indoc! {"
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
        "});
        let output = crate::instrument(asm.lines(), &cfg_result).unwrap();

        // Should have exactly 2 gas checks (one per back-edge)
        assert_eq!(output.matches("tbz x23, #63").count(), 2);

        // Both should charge for 3 instructions (no double-charging)
        assert_eq!(output.matches("sub x23, x23, #3").count(), 2);

        assert!(output.contains("b.lt .Linner"));
        assert!(output.contains("b.lt .Louter"));
    }

    #[test]
    fn test_nested_loop_instruction_counts() {
        // Inner block: add, nop, nop, cmp, b.lt = 5 instructions
        // Outer block: add, cmp, b.lt = 3 instructions
        let (cfg_result, _asm) = parse_and_build(indoc! {"
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
        "});

        // After resolution, .Linner is at index 1, .Louter is at index 0
        // (mov is at 0, add at 1, nop at 2, nop at 3, cmp at 4, b.lt at 5, ...)
        let cfg = &cfg_result.cfg;
        let mut inner_count = None;
        let mut outer_count = None;

        for block_idx in cfg.blocks() {
            if cfg.has_back_edge(block_idx) {
                let count = cfg.instruction_count(block_idx);
                // back_edge_target returns instruction index now
                // .Linner block starts at instruction index 1
                // .Louter block starts at instruction index 0
                if cfg.back_edge_target(block_idx) == Some(&1) {
                    inner_count = Some(count);
                } else if cfg.back_edge_target(block_idx) == Some(&0) {
                    outer_count = Some(count);
                }
            }
        }

        assert_eq!(inner_count, Some(5));
        assert_eq!(outer_count, Some(3));
    }

    #[test]
    fn test_label_uses_unique_prefix() {
        let (cfg_result, asm) = parse_and_build(indoc! {"
            .Lloop:
                add x0, x0, #1
                b .Lloop
        "});
        let output = crate::instrument(asm.lines(), &cfg_result).unwrap();

        assert!(output.contains(".L__gas_ok_"));
        assert!(!output.contains(".Lok_"));
    }

    #[test]
    fn test_label_collision_avoidance() {
        let (cfg_result, asm) = parse_and_build(indoc! {"
            .L__gas_ok_0:
                nop
            .L__gas_ok_1:
                nop
            .Lloop:
                add x0, x0, #1
                b .Lloop
        "});
        let output = crate::instrument(asm.lines(), &cfg_result).unwrap();

        // Should skip 0 and 1 (existing) and use 2
        assert!(output.contains(".L__gas_ok_2"));

        // Original labels preserved
        assert!(output.contains(".L__gas_ok_0:"));
        assert!(output.contains(".L__gas_ok_1:"));
    }

    #[test]
    fn test_gas_decrement_zero_count() {
        let instrumenter = Instrumenter::gas_decrement_instructions(0);
        assert!(instrumenter.is_empty());
    }

    #[test]
    fn test_gas_decrement_exact_multiple() {
        let instrumenter = Instrumenter::gas_decrement_instructions(8190);
        // 8190 = 4095 * 2, exactly 2 subs with no remainder
        assert_eq!(instrumenter.len(), 2);
        assert_eq!(instrumenter[0], "    sub x23, x23, #4095");
        assert_eq!(instrumenter[1], "    sub x23, x23, #4095");
    }

    #[test]
    fn test_self_loop_instrumentation() {
        let (cfg_result, asm) = parse_and_build(indoc! {"
            .Lspin:
                b .Lspin
        "});
        let output = crate::instrument(asm.lines(), &cfg_result).unwrap();

        assert!(output.contains("sub x23, x23, #1"));
        assert!(output.contains("tbz x23, #63"));
        assert!(output.contains("brk #0"));
        assert!(output.contains("b .Lspin"));
    }

    #[test]
    fn test_cbz_loop_instrumentation() {
        let (cfg_result, asm) = parse_and_build(indoc! {"
            _loop:
                mov x0, #10
            .Lloop:
                sub x0, x0, #1
                cbnz x0, .Lloop
                ret
        "});
        let output = crate::instrument(asm.lines(), &cfg_result).unwrap();

        assert!(output.contains("sub x23, x23, #2"));
        assert!(output.contains("cbnz x0, .Lloop"));
    }

    #[test]
    fn test_exact_gas_check_sequence() {
        let (cfg_result, asm) = parse_and_build(indoc! {"
            .Lloop:
                nop
                b .Lloop
        "});
        let output = crate::instrument(asm.lines(), &cfg_result).unwrap();

        // Verify exact sequence: original instructions, then gas check before back-edge
        let expected_sequence = indoc! {"
            .Lloop:
                nop
                sub x23, x23, #2
                tbz x23, #63, .L__gas_ok_0
                brk #0
            .L__gas_ok_0:
                b .Lloop
        "};
        assert_eq!(output.trim(), expected_sequence.trim());
    }

    #[test]
    fn test_label_on_back_edge_preserved() {
        // When the back-edge instruction has a label, it should be preserved
        let (cfg_result, asm) = parse_and_build(indoc! {"
            .Lloop:
                nop
            .Lback:
                b .Lloop
        "});
        let output = crate::instrument(asm.lines(), &cfg_result).unwrap();

        // The .Lback label should appear before the gas check
        assert!(output.contains(".Lback:"));
        // The branch should come after the gas check
        assert!(output.contains("b .Lloop"));
    }

    #[test]
    fn test_multiple_independent_loops() {
        let (cfg_result, asm) = parse_and_build(indoc! {"
            _func:
                mov x0, #0
            .Lloop1:
                add x0, x0, #1
                cmp x0, #10
                b.lt .Lloop1
                mov x1, #0
            .Lloop2:
                add x1, x1, #1
                cmp x1, #20
                b.lt .Lloop2
                ret
        "});
        let output = crate::instrument(asm.lines(), &cfg_result).unwrap();

        // Both loops should be instrumented
        assert_eq!(output.matches("tbz x23, #63").count(), 2);
        assert!(output.contains("b.lt .Lloop1"));
        assert!(output.contains("b.lt .Lloop2"));
    }

    #[test]
    fn test_label_exhaustion_returns_error() {
        // Create input with 10,001 labels that collide with our gas label prefix.
        // This exceeds MAX_LABEL_ATTEMPTS (10,000), so instrumentation should fail.
        let mut input = String::new();
        for i in 0..10_001 {
            input.push_str(&format!(".L__gas_ok_{}:\n    nop\n", i));
        }
        input.push_str(".Lloop:\n    b .Lloop\n");

        let asm = ParsedAssembly::parse(&input);
        let cfg_result = build_cfg(&asm).unwrap();
        let result = crate::instrument(asm.lines(), &cfg_result);

        assert!(
            matches!(
                result,
                Err(InstrumentError::LabelGenerationExhausted { max: 10_000 })
            ),
            "expected LabelGenerationExhausted error, got {:?}",
            result
        );
    }
}
