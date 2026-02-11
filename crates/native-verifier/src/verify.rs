//! Verification of ARM64 native code for deterministic execution
//!
//! Provides [`Verifier`] which performs the security checks described in the
//! crate-level documentation.

use std::collections::HashSet;

use cfg::{BasicInstruction, CfgInstruction, CheckResult, build_cfg};

use crate::{
    DecodedInstruction,
    error::{VerificationError, VerificationResult},
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
}

impl<'a> Verifier<'a> {
    /// Create a new verifier for the given instructions with default stack budget.
    pub fn new(instructions: &'a [DecodedInstruction]) -> Self {
        Self::with_stack_budget(instructions, DEFAULT_STACK_BUDGET)
    }

    /// Create a new verifier with a specific stack budget.
    pub fn with_stack_budget(instructions: &'a [DecodedInstruction], budget: u32) -> Self {
        let valid_offsets = instructions
            .iter()
            .map(|instruction| instruction.offset)
            .collect();
        Self {
            instructions,
            valid_offsets,
            stack_budget: budget,
        }
    }

    /// Run all verification checks in a single pass
    pub fn verify(&self) -> VerificationResult {
        let mut result = VerificationResult::default();

        for (index, instruction) in self.instructions.iter().enumerate() {
            self.check_instruction(&mut result, index, instruction);
        }

        // Build CFG once, shared by stack analysis and unreachable code check
        let cfg = build_cfg(self.instructions);

        // Stack depth analysis and multi-root unreachable code check
        let analyzer = StackAnalyzer::new(self.instructions, &cfg);
        let roots = match analyzer.verify(self.stack_budget) {
            Ok(reachable_entries) => reachable_entries,
            Err(error) => {
                result.extend([error]);
                vec![0]
            }
        };

        // Check for unreachable code.
        for block in cfg.find_unreachable_blocks(&roots) {
            let range = cfg.instruction_range(block);
            let start = self.instructions[range.start].offset;
            let end = self.instructions[range.end - 1].offset;
            result.extend([VerificationError::UnreachableCode { offset: start..end }]);
        }

        result
    }

    /// Run all checks on a single instruction
    fn check_instruction(
        &self,
        result: &mut VerificationResult,
        index: usize,
        instruction: &DecodedInstruction,
    ) {
        // Instruction whitelist
        if let CheckResult::Rejected(reason) = instruction.check() {
            result.extend([VerificationError::DisallowedInstruction {
                offset: instruction.offset,
                mnemonic: instruction.mnemonic().to_string(),
                reason: reason.to_string(),
            }]);
        }

        // Indirect branches (except ret, which is allowed)
        if instruction.is_branch() && instruction.is_indirect() && !instruction.is_return() {
            result.extend([VerificationError::IndirectBranch {
                offset: instruction.offset,
                mnemonic: instruction.mnemonic().to_string(),
            }]);
        }

        // x23 protection - only gas check sequences may touch x23
        if instruction.touches_x23()
            && !instruction.is_gas_decrement()
            && !instruction.is_gas_check_branch()
        {
            result.extend([VerificationError::InvalidGasRegisterUsage {
                offset: instruction.offset,
                mnemonic: instruction.mnemonic().to_string(),
            }]);
        }

        // SP safety - reject unbounded SP modifications
        if instruction.is_unsafe_sp_modification() {
            result.extend([VerificationError::UnsafeStackModification {
                offset: instruction.offset,
                description: format!("{}", instruction.mnemonic()),
            }]);
        }

        // Branch target validation
        if instruction.is_branch() && !instruction.is_indirect() && !instruction.is_call() {
            // Direct branch must have a valid, computable target
            match instruction.branch_target() {
                Some(target) => {
                    if !self.valid_offsets.contains(&target) {
                        result.extend([VerificationError::InvalidBranchTarget {
                            branch_offset: instruction.offset,
                            target,
                        }]);
                    }

                    // Gas sequence check (only for back-edges)
                    if target <= instruction.offset {
                        if let Some(error) = self.verify_gas_sequence_before(index, target) {
                            result.extend([error]);
                        }
                    }
                }
                None => {
                    // Direct branch with no valid target - likely negative/out-of-bounds offset
                    result.extend([VerificationError::InvalidBranchTarget {
                        branch_offset: instruction.offset,
                        target: 0, // TODO: Placeholder - actual target could not be computed
                    }]);
                }
            }
        }
    }

    /// Verify that a proper gas check sequence exists before the back-edge at `back_edge_index`
    fn verify_gas_sequence_before(
        &self,
        back_edge_index: usize,
        target_offset: usize,
    ) -> Option<VerificationError> {
        let back_edge = &self.instructions[back_edge_index];

        // We need at least 3 instructions before the back-edge
        if back_edge_index < 3 {
            return Some(VerificationError::MissingGasCheck {
                back_edge_offset: back_edge.offset,
                target_offset,
            });
        }

        // Expected sequence (working backwards from back-edge):
        // index-3: sub x23, x23, #N
        // index-2: tbz x23, #63, .Lok
        // index-1: brk #0
        // index:   <back-edge branch>

        let sub_instruction = &self.instructions[back_edge_index - 3];
        let tbz_instruction = &self.instructions[back_edge_index - 2];
        let brk_instruction = &self.instructions[back_edge_index - 1];

        if !sub_instruction.is_gas_decrement() {
            return Some(VerificationError::MalformedGasCheck {
                offset: back_edge.offset,
                reason: format!(
                    "expected 'sub x23, x23, #N' at {:#x}, found '{}'",
                    sub_instruction.offset,
                    sub_instruction.mnemonic()
                ),
            });
        }

        if !tbz_instruction.is_gas_check_branch() {
            return Some(VerificationError::MalformedGasCheck {
                offset: back_edge.offset,
                reason: format!(
                    "expected 'tbz x23, #63, ...' at {:#x}, found '{}'",
                    tbz_instruction.offset,
                    tbz_instruction.mnemonic()
                ),
            });
        }

        // tbz target should skip the brk (jump to back-edge)
        if let Some(tbz_target) = tbz_instruction.branch_target() {
            if tbz_target != back_edge.offset {
                return Some(VerificationError::MalformedGasCheck {
                    offset: back_edge.offset,
                    reason: format!(
                        "tbz at {:#x} jumps to {:#x}, expected {:#x} (back-edge)",
                        tbz_instruction.offset, tbz_target, back_edge.offset
                    ),
                });
            }
        }

        if !brk_instruction.is_brk_trap() {
            return Some(VerificationError::MalformedGasCheck {
                offset: back_edge.offset,
                reason: format!(
                    "expected 'brk #0' at {:#x}, found '{}'",
                    brk_instruction.offset,
                    brk_instruction.mnemonic()
                ),
            });
        }

        // Verify no branches target the middle of the gas sequence (tbz or brk).
        // A branch targeting tbz or brk could allow skipping the gas decrement.
        let tbz_offset = tbz_instruction.offset;
        let brk_offset = brk_instruction.offset;

        for instr in self.instructions.iter() {
            if let Some(target) = instr.branch_target() {
                if target == tbz_offset || target == brk_offset {
                    return Some(VerificationError::MalformedGasCheck {
                        offset: back_edge.offset,
                        reason: format!(
                            "branch at {:#x} targets inside gas check sequence at {:#x}",
                            instr.offset, target
                        ),
                    });
                }
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use crate::{DecodedInstruction, VerificationError, Verifier, decode_instructions};

    fn decode(bytes: &[u8]) -> Vec<DecodedInstruction> {
        decode_instructions(bytes).expect("decode failed")
    }

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
        // br x0
        let code = [0x00, 0x00, 0x1f, 0xd6];
        let result = Verifier::new(&decode(&code)).verify();

        assert!(!result.is_ok());
        assert!(
            result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::IndirectBranch { .. }))
        );
    }

    #[test]
    fn test_ret_is_allowed() {
        // ret — should NOT produce IndirectBranch error
        let code = [0xc0, 0x03, 0x5f, 0xd6];
        let result = Verifier::new(&decode(&code)).verify();

        assert!(
            !result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::IndirectBranch { .. })),
            "ret should not produce IndirectBranch error"
        );
    }

    #[test]
    fn test_detect_x23_tampering() {
        // mov x23, #1
        let code = [0x37, 0x00, 0x80, 0xd2];
        let result = Verifier::new(&decode(&code)).verify();

        assert!(!result.is_ok());
        assert!(
            result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::InvalidGasRegisterUsage { .. }))
        );
    }

    #[test]
    fn test_allow_gas_decrement() {
        // sub x23, x23, #5
        let code = [0xf7, 0x16, 0x00, 0xd1];
        let result = Verifier::new(&decode(&code)).verify();

        assert!(
            !result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::InvalidGasRegisterUsage { .. }))
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
    fn test_back_edge_without_gas_check() {
        // .Lloop: add x0, x0, #1; b .Lloop
        let code = [
            0x00, 0x04, 0x00, 0x91, // add x0, x0, #1
            0xff, 0xff, 0xff, 0x17, // b #-4
        ];
        let result = Verifier::new(&decode(&code)).verify();

        assert!(!result.is_ok());
        assert!(
            result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::MissingGasCheck { .. }))
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

    // Security tests for vulnerability fixes

    #[test]
    fn test_zero_gas_decrement_causes_error() {
        // sub x23, x23, #0 should cause InvalidGasModification
        // because it writes to x23 but is NOT a valid gas decrement
        let code = [0xf7, 0x02, 0x00, 0xd1]; // sub x23, x23, #0
        let result = Verifier::new(&decode(&code)).verify();

        assert!(!result.is_ok());
        assert!(
            result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::InvalidGasRegisterUsage { .. })),
            "sub x23, x23, #0 should be flagged as invalid gas modification"
        );
    }

    #[test]
    fn test_x23_writeback_causes_error() {
        // ldr x0, [x23], #8 should cause InvalidGasModification
        let code = [0xe0, 0x86, 0x40, 0xf8]; // ldr x0, [x23], #8
        let result = Verifier::new(&decode(&code)).verify();

        assert!(!result.is_ok());
        assert!(
            result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::InvalidGasRegisterUsage { .. })),
            "post-index writeback to x23 should be flagged as invalid gas modification"
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
    fn test_unsafe_sp_modification_detected() {
        // sub sp, sp, x0, uxtx — register-based SP modification
        let code = [0xff, 0x63, 0x20, 0xcb];
        let result = Verifier::new(&decode(&code)).verify();

        assert!(
            result
                .errors()
                .iter()
                .any(|e| matches!(e, VerificationError::UnsafeStackModification { .. })),
            "sub sp, sp, x0 should produce UnsafeStackModification"
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
}
