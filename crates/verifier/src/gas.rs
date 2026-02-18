// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Gas instrumentation verification
//!
//! Verifies that the gas counter register (x23) is only modified by valid
//! gas check sequences and that every back-edge is preceded by a gas check.

use std::collections::HashSet;

use cfg::{BasicInstruction, CfgInstruction};
use yaxpeax_arm::armv8::a64::{Opcode, Operand, SizeCode};

use crate::DecodedInstruction;
use crate::error::VerificationError;

/// Default gas budget (1 billion units).
pub const DEFAULT_GAS_BUDGET: u64 = 1_000_000_000;

/// Classification of an instruction's effect on the gas register (x23).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GasEffect {
    /// Instruction does not reference x23.
    None,
    /// Valid gas decrement: `sub x23, x23, #N` (N > 0).
    Decrement(u32),
    /// Valid gas check branch: `tbz x23, #63, <label>`.
    CheckBranch,
    /// References x23 in any other way. Must be rejected.
    Unsafe,
}

impl From<&DecodedInstruction> for GasEffect {
    fn from(instruction: &DecodedInstruction) -> Self {
        let ops = instruction.operands();
        let opcode = instruction.opcode();

        // First check for the two allowed patterns.

        // sub x23, x23, #N (N > 0) — valid gas decrement
        if matches!(opcode, Opcode::SUB | Opcode::SUBS)
            && is_register_x23(&ops[0])
            && is_register_x23(&ops[1])
        {
            return match &ops[2] {
                Operand::Immediate(n) if *n > 0 => GasEffect::Decrement(*n),
                Operand::Imm64(n) if *n > 0 => GasEffect::Decrement(*n as u32),
                _ => GasEffect::Unsafe, // sub x23, x23, #0 or non-immediate
            };
        }

        // tbz x23, #63, <label> — valid gas check branch
        if opcode == Opcode::TBZ {
            let is_bit_63 = matches!(&ops[1], Operand::Immediate(63) | Operand::Imm16(63));
            if is_register_x23(&ops[0]) && is_bit_63 {
                return GasEffect::CheckBranch;
            }
        }

        // Any other reference to x23/w23 is unsafe.
        for op in ops {
            if operand_references_x23(op) {
                return GasEffect::Unsafe;
            }
        }

        GasEffect::None
    }
}

/// Check if an operand is the register x23/w23 (as Register or RegisterOrSP).
///
/// Includes w23 (32-bit alias) because writing to w23 clears x23's upper bits,
/// which could bypass gas checks by clearing the sign bit.
fn is_register_x23(op: &Operand) -> bool {
    matches!(
        op,
        Operand::Register(SizeCode::X, 23)
            | Operand::Register(SizeCode::W, 23)
            | Operand::RegisterOrSP(SizeCode::X, 23)
            | Operand::RegisterOrSP(SizeCode::W, 23)
    )
}

/// Check if an operand references x23/w23 in any position (source, destination,
/// base, index).
///
/// Includes w23 (32-bit alias) because writing to w23 clears x23's upper bits,
/// which could bypass gas checks by clearing the sign bit.
fn operand_references_x23(op: &Operand) -> bool {
    match op {
        // Direct register uses (both 64-bit x23 and 32-bit w23)
        Operand::Register(SizeCode::X, 23)
        | Operand::Register(SizeCode::W, 23)
        | Operand::RegisterOrSP(SizeCode::X, 23)
        | Operand::RegisterOrSP(SizeCode::W, 23) => true,

        // Register pairs (ldp/stp) - both sizes
        Operand::RegisterPair(SizeCode::X, reg) | Operand::RegisterPair(SizeCode::W, reg)
            if *reg == 23 =>
        {
            true
        }

        // Register with shift (e.g., x23, lsl #3 in add x0, x1, x23, lsl #3)
        Operand::RegShift(_, _, SizeCode::X, 23) | Operand::RegShift(_, _, SizeCode::W, 23) => true,

        // Memory addressing - x23 as base (all forms)
        Operand::RegPreIndex(23, _, _)
        | Operand::RegPostIndex(23, _)
        | Operand::RegPostIndexReg(23, _) => true,

        // Memory addressing - x23 as offset register in post-index
        Operand::RegPostIndexReg(_, 23) => true,

        // Memory addressing - x23 as base or index in register offset mode
        Operand::RegRegOffset(base, idx, _, _, _) if *base == 23 || *idx == 23 => true,

        _ => false,
    }
}

/// Analyzes gas instrumentation for a sequence of decoded instructions.
pub struct GasAnalyzer<'a> {
    instructions: &'a [DecodedInstruction],
}

impl<'a> GasAnalyzer<'a> {
    pub fn new(instructions: &'a [DecodedInstruction]) -> Self {
        Self { instructions }
    }

    /// Verify all gas instrumentation invariants.
    ///
    /// On success, returns the minimum gas decrement amount found (needed by
    /// `StackAnalyzer` to bound loop iterations). Returns 0 if no gas
    /// decrements exist (program has no loops).
    pub fn verify(&self) -> Result<u32, Vec<VerificationError>> {
        let mut errors = Vec::new();
        let mut min_gas_decrement: u32 = 0;
        let mut protected_offsets: HashSet<usize> = HashSet::new();

        for (index, instruction) in self.instructions.iter().enumerate() {
            let effect = GasEffect::from(instruction);

            // x23 protection: only gas check sequences may touch x23
            if effect == GasEffect::Unsafe {
                errors.push(VerificationError::InvalidGasRegisterUsage {
                    offset: instruction.offset,
                    mnemonic: instruction.mnemonic().to_string(),
                });
            }

            // Track minimum gas decrement
            if let GasEffect::Decrement(amount) = effect {
                if min_gas_decrement == 0 {
                    min_gas_decrement = amount;
                } else {
                    min_gas_decrement = min_gas_decrement.min(amount);
                }
            }

            // Back-edge gas sequence verification
            if instruction.is_branch() && !instruction.is_indirect() && !instruction.is_call() {
                match instruction.branch_target() {
                    Some(target) if target <= instruction.offset => {
                        match self.verify_gas_sequence_before(index, target) {
                            Ok((tbz_off, brk_off)) => {
                                protected_offsets.insert(tbz_off);
                                protected_offsets.insert(brk_off);
                            }
                            Err(error) => errors.push(error),
                        }
                    }
                    Some(_) => {} // forward branch — no gas check needed
                    None => {
                        // Target is unresolvable (e.g. negative offset).
                        // Flag it: we can't rule out a back-edge.
                        errors.push(VerificationError::InvalidBranchTarget {
                            branch_offset: instruction.offset,
                            target: 0,
                        });
                    }
                }
            }
        }

        // Verify no branches target the middle of any gas sequence.
        // A branch targeting tbz or brk could skip the gas decrement.
        if !protected_offsets.is_empty() {
            for instruction in self.instructions.iter() {
                if let Some(target) = instruction.branch_target() {
                    if protected_offsets.contains(&target) {
                        errors.push(VerificationError::BranchIntoGasSequence {
                            branch_offset: instruction.offset,
                            target_offset: target,
                        });
                    }
                }
            }
        }

        if errors.is_empty() {
            Ok(min_gas_decrement)
        } else {
            Err(errors)
        }
    }

    /// Verify that a proper gas check sequence exists before the back-edge at
    /// `back_edge_index`.
    ///
    /// On success, returns the offsets of the tbz and brk instructions
    /// (protected offsets that no branch may target).
    fn verify_gas_sequence_before(
        &self,
        back_edge_index: usize,
        target_offset: usize,
    ) -> Result<(usize, usize), VerificationError> {
        let back_edge = &self.instructions[back_edge_index];

        // We need at least 3 instructions before the back-edge
        if back_edge_index < 3 {
            return Err(VerificationError::MissingGasCheck {
                back_edge_offset: back_edge.offset,
                target_offset,
            });
        }

        // Expected sequence (working backwards from back-edge):
        // index-3: sub x23, x23, #N
        // index-2: tbz x23, #63, .Look
        // index-1: brk #0
        // index:   <back-edge branch>

        let sub_instruction = &self.instructions[back_edge_index - 3];
        let tbz_instruction = &self.instructions[back_edge_index - 2];
        let brk_instruction = &self.instructions[back_edge_index - 1];

        if !matches!(GasEffect::from(sub_instruction), GasEffect::Decrement(_)) {
            return Err(VerificationError::GasSequenceUnexpectedInstruction {
                back_edge_offset: back_edge.offset,
                position_offset: sub_instruction.offset,
                expected: "sub x23, x23, #N",
                found: sub_instruction.mnemonic().to_string(),
            });
        }

        if GasEffect::from(tbz_instruction) != GasEffect::CheckBranch {
            return Err(VerificationError::GasSequenceUnexpectedInstruction {
                back_edge_offset: back_edge.offset,
                position_offset: tbz_instruction.offset,
                expected: "tbz x23, #63, ...",
                found: tbz_instruction.mnemonic().to_string(),
            });
        }

        // tbz target should skip the brk (jump to back-edge)
        if let Some(tbz_target) = tbz_instruction.branch_target() {
            if tbz_target != back_edge.offset {
                return Err(VerificationError::GasSequenceBadTarget {
                    back_edge_offset: back_edge.offset,
                    tbz_offset: tbz_instruction.offset,
                    actual_target: tbz_target,
                    expected_target: back_edge.offset,
                });
            }
        }

        if !brk_instruction.is_brk_trap() {
            return Err(VerificationError::GasSequenceUnexpectedInstruction {
                back_edge_offset: back_edge.offset,
                position_offset: brk_instruction.offset,
                expected: "brk #0",
                found: brk_instruction.mnemonic().to_string(),
            });
        }

        Ok((tbz_instruction.offset, brk_instruction.offset))
    }
}

#[cfg(test)]
mod tests {
    use crate::{VerificationError, decode::decode_instructions_unchecked as decode};

    use super::{GasAnalyzer, GasEffect};

    #[test]
    fn test_gas_decrement() {
        // sub x23, x23, #3
        let code = [0xf7, 0x0e, 0x00, 0xd1];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Decrement(3));
    }

    #[test]
    fn test_gas_decrement_amount_5() {
        // sub x23, x23, #5
        let code = [0xf7, 0x16, 0x00, 0xd1];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Decrement(5));
    }

    #[test]
    fn test_sub_other_register_not_gas() {
        // sub x0, x0, #3
        let code = [0x00, 0x0c, 0x00, 0xd1];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::None);
    }

    #[test]
    fn test_gas_check_branch_tbz() {
        // tbz x23, #63, #8
        let code = [0x97, 0x00, 0xf8, 0xb6];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::CheckBranch);
    }

    #[test]
    fn test_zero_gas_decrement_is_unsafe() {
        // sub x23, x23, #0
        let code = [0xf7, 0x02, 0x00, 0xd1];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Unsafe);
    }

    #[test]
    fn test_mov_x23_is_unsafe() {
        // mov x23, #1 (MOVZ x23, #1)
        let code = [0x37, 0x00, 0x80, 0xd2];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Unsafe);
    }

    #[test]
    fn test_add_x23_is_unsafe() {
        // add x23, x23, #1
        let code = [0xf7, 0x06, 0x00, 0x91];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Unsafe);
    }

    #[test]
    fn test_writeback_post_index_load_is_unsafe() {
        // ldr x0, [x23], #8
        let code = [0xe0, 0x86, 0x40, 0xf8];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Unsafe);
    }

    #[test]
    fn test_writeback_post_index_store_is_unsafe() {
        // str x0, [x23], #8
        let code = [0xe0, 0x86, 0x00, 0xf8];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Unsafe);
    }

    #[test]
    fn test_writeback_pre_index_is_unsafe() {
        // ldr x0, [x23, #8]!
        let code = [0xe0, 0x8e, 0x40, 0xf8];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Unsafe);
    }

    #[test]
    fn test_x23_as_base_no_writeback_is_unsafe() {
        // ldr x0, [x23, #8] (no writeback)
        let code = [0xe0, 0x06, 0x40, 0xf9];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Unsafe);
    }

    #[test]
    fn test_str_x23_is_unsafe() {
        // str x23, [sp]
        let code = [0xf7, 0x03, 0x00, 0xf9];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Unsafe);
    }

    #[test]
    fn test_x23_as_source_operand_is_unsafe() {
        // add x0, x1, x23
        let code = [0x20, 0x00, 0x17, 0x8b];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Unsafe);
    }

    #[test]
    fn test_w23_mov_is_unsafe() {
        // mov w23, #1 (MOVZ w23, #1)
        let code = [0x37, 0x00, 0x80, 0x52];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Unsafe);
    }

    #[test]
    fn test_w23_add_is_unsafe() {
        // add w23, w23, #1
        let code = [0xf7, 0x06, 0x00, 0x11];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Unsafe);
    }

    #[test]
    fn test_non_x23_instruction_is_none() {
        // mov x0, #0
        let code = [0x00, 0x00, 0x80, 0xd2];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::None);
    }

    #[test]
    fn test_analyzer_x23_tampering() {
        // mov x23, #1
        let code = [0x37, 0x00, 0x80, 0xd2];
        let instructions = decode(&code);
        let result = GasAnalyzer::new(&instructions).verify();

        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .iter()
                .any(|e| matches!(e, VerificationError::InvalidGasRegisterUsage { .. }))
        );
    }

    #[test]
    fn test_analyzer_allow_gas_decrement() {
        // sub x23, x23, #5
        let code = [0xf7, 0x16, 0x00, 0xd1];
        let instructions = decode(&code);
        let result = GasAnalyzer::new(&instructions).verify();

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 5);
    }

    #[test]
    fn test_analyzer_back_edge_without_gas_check() {
        // .Lloop: add x0, x0, #1; b .Lloop
        let code = [
            0x00, 0x04, 0x00, 0x91, // add x0, x0, #1
            0xff, 0xff, 0xff, 0x17, // b #-4
        ];
        let instructions = decode(&code);
        let result = GasAnalyzer::new(&instructions).verify();

        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .iter()
                .any(|e| matches!(e, VerificationError::MissingGasCheck { .. }))
        );
    }

    #[test]
    fn test_analyzer_zero_gas_decrement() {
        // sub x23, x23, #0 should cause InvalidGasRegisterUsage
        let code = [0xf7, 0x02, 0x00, 0xd1];
        let instructions = decode(&code);
        let result = GasAnalyzer::new(&instructions).verify();

        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .iter()
                .any(|e| matches!(e, VerificationError::InvalidGasRegisterUsage { .. })),
            "sub x23, x23, #0 should be flagged as invalid gas modification"
        );
    }

    #[test]
    fn test_analyzer_x23_writeback() {
        // ldr x0, [x23], #8
        let code = [0xe0, 0x86, 0x40, 0xf8];
        let instructions = decode(&code);
        let result = GasAnalyzer::new(&instructions).verify();

        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .iter()
                .any(|e| matches!(e, VerificationError::InvalidGasRegisterUsage { .. })),
            "post-index writeback to x23 should be flagged as invalid gas modification"
        );
    }

    #[test]
    fn test_analyzer_min_gas_decrement() {
        // sub x23, x23, #10; sub x23, x23, #3
        let code = [
            0xf7, 0x2a, 0x00, 0xd1, // sub x23, x23, #10
            0xf7, 0x0e, 0x00, 0xd1, // sub x23, x23, #3
        ];
        let instructions = decode(&code);
        let result = GasAnalyzer::new(&instructions).verify();

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 3);
    }

    #[test]
    fn test_analyzer_no_gas_decrements() {
        // mov x0, #0; ret
        let code = [
            0x00, 0x00, 0x80, 0xd2, // mov x0, #0
            0xc0, 0x03, 0x5f, 0xd6, // ret
        ];
        let instructions = decode(&code);
        let result = GasAnalyzer::new(&instructions).verify();

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 0);
    }

    #[test]
    fn test_analyzer_valid_gas_sequence() {
        // Complete valid gas check before a back-edge:
        //   [0]  nop               (loop body)
        //   [4]  sub x23, x23, #3  (gas decrement)
        //   [8]  tbz x23, #63, +8  (check → skip brk, target=16)
        //   [12] brk #0            (trap)
        //   [16] b.lt -16          (back-edge → 0)
        let code = [
            0x1f, 0x20, 0x03, 0xd5, // nop
            0xf7, 0x0e, 0x00, 0xd1, // sub x23, x23, #3
            0x57, 0x00, 0xf8, 0xb6, // tbz x23, #63, +8
            0x00, 0x00, 0x20, 0xd4, // brk #0
            0x8b, 0xff, 0xff, 0x54, // b.lt -16
        ];
        let instructions = decode(&code);
        let result = GasAnalyzer::new(&instructions).verify();

        assert!(
            result.is_ok(),
            "valid gas sequence should pass: {:?}",
            result.unwrap_err()
        );
        assert_eq!(result.unwrap(), 3);
    }

    #[test]
    fn test_analyzer_wrong_instruction_in_sequence() {
        // Back-edge with 3+ instructions before it, but they're all nops (not a gas sequence):
        //   [0]  nop
        //   [4]  nop   ← expected sub x23
        //   [8]  nop
        //   [12] nop
        //   [16] b -16  (back-edge → 0)
        let code = [
            0x1f, 0x20, 0x03, 0xd5, // nop
            0x1f, 0x20, 0x03, 0xd5, // nop
            0x1f, 0x20, 0x03, 0xd5, // nop
            0x1f, 0x20, 0x03, 0xd5, // nop
            0xfc, 0xff, 0xff, 0x17, // b -16
        ];
        let instructions = decode(&code);
        let result = GasAnalyzer::new(&instructions).verify();

        assert!(result.is_err());
        assert!(
            result.unwrap_err().iter().any(|e| matches!(
                e,
                VerificationError::GasSequenceUnexpectedInstruction { .. }
            )),
            "should report wrong instruction in gas sequence position"
        );
    }

    #[test]
    fn test_analyzer_tbz_bad_target() {
        // Valid sub/tbz/brk but tbz targets the wrong offset:
        //   [0]  nop
        //   [4]  sub x23, x23, #3
        //   [8]  tbz x23, #63, +12  (targets 20, should target 16)
        //   [12] brk #0
        //   [16] b.lt -16           (back-edge → 0)
        let code = [
            0x1f, 0x20, 0x03, 0xd5, // nop
            0xf7, 0x0e, 0x00, 0xd1, // sub x23, x23, #3
            0x77, 0x00, 0xf8, 0xb6, // tbz x23, #63, +12
            0x00, 0x00, 0x20, 0xd4, // brk #0
            0x8b, 0xff, 0xff, 0x54, // b.lt -16
        ];
        let instructions = decode(&code);
        let result = GasAnalyzer::new(&instructions).verify();

        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .iter()
                .any(|e| matches!(e, VerificationError::GasSequenceBadTarget { .. })),
            "should report tbz targeting wrong offset"
        );
    }

    #[test]
    fn test_sub_x23_register_operand_is_unsafe() {
        // sub x23, x23, x0 (register operand, not immediate)
        let code = [0xf7, 0x02, 0x00, 0xcb];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Unsafe);
    }

    #[test]
    fn test_tbz_wrong_bit_is_not_gas_check() {
        // tbz x23, #62, +8 (bit 62, not 63 — not a valid gas check)
        let code = [0x57, 0x00, 0xf0, 0xb6];
        let instructions = decode(&code);
        // tbz with bit != 63 references x23 → Unsafe
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Unsafe);
    }

    #[test]
    fn test_ldp_w23_pair_is_unsafe() {
        // ldp w23, w24, [sp] (RegisterPair with w23)
        let code = [0xf7, 0x63, 0x40, 0x29];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Unsafe);
    }

    #[test]
    fn test_ldr_register_offset_x23_is_unsafe() {
        // ldr x0, [x1, x23] (x23 as index register in RegRegOffset)
        let code = [0x20, 0x68, 0x77, 0xf8];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Unsafe);
    }

    #[test]
    fn test_add_x23_shifted_register_is_unsafe() {
        // add x0, x1, x23, lsl #3 (x23 in RegShift operand)
        let code = [0x20, 0x0c, 0x17, 0x8b];
        let instructions = decode(&code);
        assert_eq!(GasEffect::from(&instructions[0]), GasEffect::Unsafe);
    }

    #[test]
    fn test_analyzer_brk_nonzero_in_gas_sequence() {
        // Gas sequence with brk #1 instead of brk #0:
        //   [0]  nop
        //   [4]  sub x23, x23, #3
        //   [8]  tbz x23, #63, +8 (target = 16)
        //   [12] brk #1             (wrong trap value)
        //   [16] b.lt -16           (back-edge → 0)
        let code = [
            0x1f, 0x20, 0x03, 0xd5, // nop
            0xf7, 0x0e, 0x00, 0xd1, // sub x23, x23, #3
            0x57, 0x00, 0xf8, 0xb6, // tbz x23, #63, +8
            0x20, 0x00, 0x20, 0xd4, // brk #1
            0x8b, 0xff, 0xff, 0x54, // b.lt -16
        ];
        let instructions = decode(&code);
        let result = GasAnalyzer::new(&instructions).verify();

        assert!(result.is_err());
        assert!(
            result.unwrap_err().iter().any(|e| matches!(
                e,
                VerificationError::GasSequenceUnexpectedInstruction {
                    expected: "brk #0",
                    ..
                }
            )),
            "brk #1 should not be accepted as gas trap"
        );
    }

    #[test]
    fn test_analyzer_backward_branch_from_zero() {
        // b #-4 at offset 0: target = 0 + (-4) = -4 → unresolvable (negative)
        let code = [0xff, 0xff, 0xff, 0x17]; // b #-4
        let instructions = decode(&code);
        let result = GasAnalyzer::new(&instructions).verify();

        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .iter()
                .any(|e| matches!(e, VerificationError::InvalidBranchTarget { .. })),
            "backward branch with unresolvable target should be rejected"
        );
    }

    #[test]
    fn test_analyzer_branch_into_gas_sequence() {
        // A branch targets the tbz inside a valid gas sequence:
        //   [0]  b +12              (targets 12 = protected tbz offset)
        //   [4]  nop                (loop body / back-edge target)
        //   [8]  sub x23, x23, #3
        //   [12] tbz x23, #63, +8   (targets 20)  ← protected
        //   [16] brk #0                            ← protected
        //   [20] b.lt -16           (back-edge → 4)
        let code = [
            0x03, 0x00, 0x00, 0x14, // b +12
            0x1f, 0x20, 0x03, 0xd5, // nop
            0xf7, 0x0e, 0x00, 0xd1, // sub x23, x23, #3
            0x57, 0x00, 0xf8, 0xb6, // tbz x23, #63, +8
            0x00, 0x00, 0x20, 0xd4, // brk #0
            0x8b, 0xff, 0xff, 0x54, // b.lt -16
        ];
        let instructions = decode(&code);
        let result = GasAnalyzer::new(&instructions).verify();

        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .iter()
                .any(|e| matches!(e, VerificationError::BranchIntoGasSequence { .. })),
            "should report branch into gas check sequence"
        );
    }
}
