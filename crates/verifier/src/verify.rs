// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Verification of ARM64 native code for deterministic execution
//!
//! Provides [`Verifier`] which performs the security checks described in the
//! crate-level documentation.

use std::collections::HashSet;

use cfg::{BasicInstruction, CfgInstruction, CheckResult, build_call_graph};

use crate::{
    DecodedInstruction,
    error::{VerificationError, VerificationResult},
    gas::{DEFAULT_GAS_BUDGET, GasAnalyzer},
    stack::{DEFAULT_STACK_BUDGET, StackAnalyzer},
};

/// Verifier for ARM64 native code
///
/// Performs all security checks required for deterministic execution.
pub struct Verifier<'a> {
    instructions: &'a [DecodedInstruction],
    /// Set of valid instruction offsets for branch target validation
    valid_offsets: HashSet<usize>,
    /// Stack depth budget in bytes.
    stack_budget: u32,
    /// Gas budget used to bound worst-case loop iterations for stack analysis.
    gas_budget: u64,
}

impl<'a> Verifier<'a> {
    /// Create a new verifier for the given instructions with default budgets.
    pub fn new(instructions: &'a [DecodedInstruction]) -> Self {
        let valid_offsets = instructions
            .iter()
            .map(|instruction| instruction.offset)
            .collect();
        Self {
            instructions,
            valid_offsets,
            stack_budget: DEFAULT_STACK_BUDGET,
            gas_budget: DEFAULT_GAS_BUDGET,
        }
    }

    /// Create a new verifier with specific stack and gas budgets (testing only).
    pub fn with_budgets(
        instructions: &'a [DecodedInstruction],
        stack_budget: u32,
        gas_budget: u64,
    ) -> Self {
        let valid_offsets = instructions
            .iter()
            .map(|instruction| instruction.offset)
            .collect();
        Self {
            instructions,
            valid_offsets,
            stack_budget,
            gas_budget,
        }
    }

    /// Run all verification checks
    pub fn verify(&self) -> VerificationResult {
        let mut result = VerificationResult::default();

        for instruction in self.instructions.iter() {
            // Instruction whitelist
            if let CheckResult::Rejected(reason) = instruction.check() {
                result.extend([VerificationError::DisallowedInstruction {
                    offset: instruction.offset,
                    mnemonic: instruction.mnemonic().to_string(),
                    reason: reason.to_string(),
                }]);
            }

            // Branch target validation
            if instruction.is_branch() && !instruction.is_indirect() && !instruction.is_call() {
                match instruction.branch_target() {
                    Some(target) => {
                        if !self.valid_offsets.contains(&target) {
                            result.extend([VerificationError::InvalidBranchTarget {
                                branch_offset: instruction.offset,
                                target,
                            }]);
                        }
                    }
                    None => {
                        result.extend([VerificationError::InvalidBranchTarget {
                            branch_offset: instruction.offset,
                            target: 0, // TODO: Placeholder - actual target could not be computed
                        }]);
                    }
                }
            }
        }

        // Gas instrumentation analysis
        let gas = GasAnalyzer::new(self.instructions);
        let min_gas_decrement = match gas.verify() {
            Ok(min) => min,
            Err(errors) => {
                result.extend(errors);
                0
            }
        };

        // Build CFG once (block graph + call-cycle detection), shared by all analyses
        let (cfg, call_cycle) = build_call_graph(self.instructions);

        // Recursion creates inter-procedural loops with no gas decrements,
        // bypassing gas metering entirely. Reject cyclic call graphs.
        if let Some(cycle_entry) = call_cycle {
            result.extend([VerificationError::RecursiveCallGraph { cycle_entry }]);
        }

        // Check for unreachable code.
        // The CFG follows call targets (bl) during reachability, so &[0] suffices.
        for block in cfg.compute_unreachable(&[0]) {
            let range = cfg.instruction_range(block);
            let start = self.instructions[range.start].offset;
            let end = self.instructions[range.end - 1].offset;
            result.extend([VerificationError::UnreachableCode { offset: start..end }]);
        }

        // Stack analysis (SP safety + depth budget)
        let analyzer = StackAnalyzer::new(self.instructions);
        let (stack_errors, _) =
            analyzer.verify(self.stack_budget, self.gas_budget, min_gas_decrement);
        result.extend(stack_errors);

        result
    }
}

#[cfg(test)]
mod tests {
    use crate::{VerificationError, Verifier, decode::decode_instructions_unchecked as decode};

    #[test]
    fn test_verify_empty_code() {
        let result = Verifier::new(&decode(&[])).verify();
        assert!(result.is_ok());
    }

    #[test]
    fn test_verify_simple_code() {
        // mov x0, #0
        let code = [0x00, 0x00, 0x80, 0xd2];
        let result = Verifier::new(&decode(&code)).verify();
        assert!(result.is_ok(), "mov x0, #0 should be allowed");
    }

    #[test]
    fn test_detect_indirect_branch_br() {
        // br x0 — rejected by instruction whitelist
        let code = [0x00, 0x00, 0x1f, 0xd6];
        let result = Verifier::new(&decode(&code)).verify();

        assert!(!result.is_ok());
        assert!(
            result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::DisallowedInstruction { .. }))
        );
    }

    #[test]
    fn test_ret_is_allowed() {
        // ret — allowed by instruction whitelist
        let code = [0xc0, 0x03, 0x5f, 0xd6];
        let result = Verifier::new(&decode(&code)).verify();

        assert!(
            !result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::DisallowedInstruction { .. })),
            "ret should not produce DisallowedInstruction error"
        );
    }

    #[test]
    fn test_valid_branch_target() {
        // b #4; nop
        let code = [
            0x01, 0x00, 0x00, 0x14, // b #4
            0x1f, 0x20, 0x03, 0xd5, // nop
        ];
        let result = Verifier::new(&decode(&code)).verify();

        assert!(
            !result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::InvalidBranchTarget { .. }))
        );
    }

    #[test]
    fn test_detect_unreachable_code() {
        // b #8; nop; nop (second nop is unreachable)
        let code = [
            0x02, 0x00, 0x00, 0x14, // b #8 (skip to third instruction)
            0x1f, 0x20, 0x03, 0xd5, // nop (unreachable)
            0x1f, 0x20, 0x03, 0xd5, // nop (reachable via jump)
        ];
        let result = Verifier::new(&decode(&code)).verify();

        assert!(!result.is_ok());
        let unreachable_errors: Vec<_> = result
            .errors()
            .iter()
            .filter(|e| matches!(e, VerificationError::UnreachableCode { .. }))
            .collect();
        assert!(
            !unreachable_errors.is_empty(),
            "should detect unreachable code"
        );
        // The unreachable block spans offset 4
        assert!(result.errors().iter().any(
            |e| matches!(e, VerificationError::UnreachableCode { offset } if offset.start == 4)
        ));
    }

    #[test]
    fn test_all_code_reachable_no_error() {
        // Simple sequential code: all reachable
        let code = [
            0x1f, 0x20, 0x03, 0xd5, // nop
            0x1f, 0x20, 0x03, 0xd5, // nop
        ];
        let result = Verifier::new(&decode(&code)).verify();

        assert!(
            !result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::UnreachableCode { .. }))
        );
    }

    #[test]
    fn test_branch_to_out_of_bounds_negative() {
        // A branch at offset 0 that tries to branch to a negative address
        // b #-4 at offset 0 would target -4 which is invalid
        // b #-4 -> 0x17ffffff
        let code = [0xff, 0xff, 0xff, 0x17];
        let result = Verifier::new(&decode(&code)).verify();

        assert!(!result.is_ok());
        assert!(
            result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::InvalidBranchTarget { .. })),
            "branch to negative address should be rejected"
        );
    }

    #[test]
    fn test_multi_function_no_false_unreachable() {
        // Two functions: func1 calls func2, func2 code after func1's ret
        // func1: bl func2; ret
        // func2: mov x0, #0; ret
        //
        // Without multi-root BFS, func2 would be flagged as unreachable
        // because ret terminates the block and there's no fall-through.
        let code = [
            0x02, 0x00, 0x00, 0x94, // bl #8 (→ offset 8)  [0]
            0xc0, 0x03, 0x5f, 0xd6, // ret                  [4]
            0x00, 0x00, 0x80, 0xd2, // mov x0, #0           [8]
            0xc0, 0x03, 0x5f, 0xd6, // ret                  [12]
        ];
        let result = Verifier::new(&decode(&code)).verify();

        assert!(
            !result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::UnreachableCode { .. })),
            "func2 should not be flagged as unreachable: errors = {:?}",
            result.errors()
        );
    }

    #[test]
    fn test_cycle_detection_via_bl() {
        // Two functions that call each other via bl:
        // func_a [0]: bl func_b (→8); ret
        // func_b [8]: bl func_a (→0); ret
        let code = [
            0x02, 0x00, 0x00, 0x94, // bl #2 (→8)          [0]
            0xc0, 0x03, 0x5f, 0xd6, // ret                  [4]
            0xfe, 0xff, 0xff, 0x97, // bl #-2 (→0)          [8]
            0xc0, 0x03, 0x5f, 0xd6, // ret                  [12]
        ];
        let result = Verifier::new(&decode(&code)).verify();
        assert!(!result.is_ok());
        assert!(
            result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::RecursiveCallGraph { .. })),
            "should detect recursive call graph via bl: {:?}",
            result.errors()
        );
    }

    #[test]
    fn test_cycle_detection_via_tail_call() {
        // func_a calls func_b via bl, func_b tail-calls func_a via b.
        // This is a cycle: A → B → A (where B→A is a tail call).
        //
        // func_a [0]: bl func_b (→8)
        // func_a [4]: ret
        // func_b [8]: b func_a (→0)   ← tail call
        let code = [
            0x02, 0x00, 0x00, 0x94, // bl #2 (→8)          [0]
            0xc0, 0x03, 0x5f, 0xd6, // ret                  [4]
            0xfe, 0xff, 0xff, 0x17, // b #-2 (→0)           [8]
        ];
        let result = Verifier::new(&decode(&code)).verify();
        assert!(!result.is_ok());
        assert!(
            result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::RecursiveCallGraph { .. })),
            "should detect recursive call graph via tail call: {:?}",
            result.errors()
        );
    }

    #[test]
    fn test_self_recursive_bl_detected() {
        // Single function that calls itself via bl:
        // func_a [0]: nop
        // func_a [4]: bl func_a (→0)
        // func_a [8]: ret
        let code = [
            0x1f, 0x20, 0x03, 0xd5, // nop                   [0]
            0xff, 0xff, 0xff, 0x97, // bl #-1 (→0)            [4]
            0xc0, 0x03, 0x5f, 0xd6, // ret                    [8]
        ];
        let result = Verifier::new(&decode(&code)).verify();
        assert!(
            result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::RecursiveCallGraph { .. })),
            "should detect self-recursive bl: {:?}",
            result.errors()
        );
    }

    #[test]
    fn test_acyclic_call_chain_no_false_positive() {
        // A calls B, B calls C — no cycle.
        // func_a [0]:  bl func_b (→8); ret
        // func_b [8]:  bl func_c (→16); ret
        // func_c [16]: mov x0, #0; ret
        let code = [
            0x02, 0x00, 0x00, 0x94, // bl #2 (→8)           [0]
            0xc0, 0x03, 0x5f, 0xd6, // ret                   [4]
            0x02, 0x00, 0x00, 0x94, // bl #2 (→16)           [8]
            0xc0, 0x03, 0x5f, 0xd6, // ret                   [12]
            0x00, 0x00, 0x80, 0xd2, // mov x0, #0            [16]
            0xc0, 0x03, 0x5f, 0xd6, // ret                   [20]
        ];
        let result = Verifier::new(&decode(&code)).verify();
        assert!(
            !result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::RecursiveCallGraph { .. })),
            "acyclic call chain should not be flagged: {:?}",
            result.errors()
        );
    }

    #[test]
    fn test_branch_to_out_of_bounds_forward() {
        // b #8 as the only instruction — target offset 8 is past end of code
        let code = [0x02, 0x00, 0x00, 0x14]; // b #8
        let result = Verifier::new(&decode(&code)).verify();

        assert!(!result.is_ok());
        assert!(
            result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::InvalidBranchTarget { .. })),
            "forward branch past end of code should be rejected"
        );
    }

    #[test]
    fn test_self_recursive_tail_call_caught_by_gas_check() {
        // Function branches to its own entry via b (tail-call self-recursion).
        // The call graph does NOT detect this (successor_target == entry is
        // treated as intra-function). But the gas check verifier catches it
        // because b→0 is a backward branch requiring a gas check sequence.
        //
        // func_a [0]: cmp x0, #0
        // func_a [4]: b.eq 12        (skip to ret)
        // func_a [8]: b 0            (self-recursive tail call, backward)
        // func_a [12]: ret
        let code = [
            0x1f, 0x00, 0x00, 0xf1, // cmp x0, #0            [0]
            0x40, 0x00, 0x00, 0x54, // b.eq #8 (→12)          [4]
            0xfe, 0xff, 0xff, 0x17, // b #-2 (→0)             [8]
            0xc0, 0x03, 0x5f, 0xd6, // ret                    [12]
        ];
        let result = Verifier::new(&decode(&code)).verify();
        // Not detected as RecursiveCallGraph...
        assert!(
            !result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::RecursiveCallGraph { .. })),
            "self-recursive tail call is intra-function, not a call graph cycle"
        );
        // ...but caught as a backward branch missing a gas check
        assert!(
            result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::MissingGasCheck { .. })),
            "backward branch to own entry should require gas check: {:?}",
            result.errors()
        );
    }
}
