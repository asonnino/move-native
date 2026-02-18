//! Static stack depth verification
//!
//! Verifies that the total stack usage cannot exceed a budget.

use cfg::{BasicInstruction, CfgInstruction};
use yaxpeax_arm::armv8::a64::{Opcode, Operand, SizeCode};

use crate::DecodedInstruction;

use crate::error::VerificationError;

/// Default stack budget in bytes (1 MiB).
///
/// This is generous for Move programs which have bounded call depth.
/// The actual OS thread stack is typically 8 MiB, so 1 MiB leaves plenty
/// of headroom for the runtime, signal handlers, and native functions.
pub const DEFAULT_STACK_BUDGET: u32 = 1024 * 1024;

/// Classification of an instruction's effect on the stack pointer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpEffect {
    /// Instruction does not modify SP.
    None,
    /// Safe SP decrement by `N` bytes (stack allocation).
    ///
    /// Recognized patterns:
    /// - `sub sp, sp, #N`
    /// - `stp Xt, Xt2, [sp, #-N]!` (negative pre-index)
    /// - `str Xt, [sp, #-N]!` (negative pre-index)
    Decrement(u32),
    /// Safe SP increment (stack deallocation). Amount is irrelevant for budget.
    ///
    /// Recognized patterns:
    /// - `add sp, sp, #N`
    /// - `ldp Xt, Xt2, [sp], #+N` (positive post-index)
    /// - `ldr Xt, [sp], #+N` (positive post-index)
    Increment,
    /// Modifies SP in an unrecognized way. Must be rejected.
    Unsafe,
}

impl From<&DecodedInstruction> for SpEffect {
    /// Classify a decoded instruction's effect on the stack pointer.
    fn from(instruction: &DecodedInstruction) -> Self {
        let ops = instruction.operands();
        let opcode = instruction.opcode();

        // Check for SP as explicit destination (first operand).
        // Exclude store opcodes where operands[0] is the value being stored, not a destination.
        let sp_is_destination = !instruction.is_store()
            && matches!(
                ops[0],
                Operand::RegisterOrSP(SizeCode::X, 31) | Operand::RegisterOrSP(SizeCode::W, 31)
            );

        // Check for SP writeback (pre-index, post-index).
        let has_sp_writeback = ops.iter().any(|op| {
            matches!(
                op,
                Operand::RegPreIndex(31, _, true)
                    | Operand::RegPostIndex(31, _)
                    | Operand::RegPostIndexReg(31, _)
            )
        });

        if !sp_is_destination && !has_sp_writeback {
            return SpEffect::None;
        }

        // SP is modified — classify the pattern.
        // Each arm returns Some for a recognized safe pattern, None otherwise.
        const SP: &Operand = &Operand::RegisterOrSP(SizeCode::X, 31);

        match (opcode, &ops[0], &ops[1], &ops[2]) {
            // sub sp, sp, #N — allocation
            (Opcode::SUB, SP, SP, Operand::Immediate(n)) => SpEffect::Decrement(*n),
            (Opcode::SUB, SP, SP, Operand::Imm64(n)) => SpEffect::Decrement(*n as u32),
            // add sp, sp, #N — deallocation
            (Opcode::ADD, SP, SP, Operand::Immediate(_) | Operand::Imm64(_)) => SpEffect::Increment,
            // stp Xt, Xt2, [sp, #-N]! — pre-index store pair (negative offset only)
            (Opcode::STP, _, _, Operand::RegPreIndex(31, off, true)) if *off < 0 => {
                SpEffect::Decrement((-off) as u32)
            }
            // ldp Xt, Xt2, [sp], #+N — post-index load pair (positive offset only)
            (Opcode::LDP, _, _, Operand::RegPostIndex(31, off)) if *off >= 0 => SpEffect::Increment,
            // str Xt, [sp, #-N]! — pre-index store (negative offset only)
            (Opcode::STR, _, Operand::RegPreIndex(31, off, true), _) if *off < 0 => {
                SpEffect::Decrement((-off) as u32)
            }
            // ldr Xt, [sp], #+N — post-index load (positive offset only)
            (Opcode::LDR, _, Operand::RegPostIndex(31, off), _) if *off >= 0 => SpEffect::Increment,
            _ => SpEffect::Unsafe,
        }
    }
}

/// Analyzes stack depth for a sequence of decoded instructions.
pub struct StackAnalyzer<'a> {
    instructions: &'a [DecodedInstruction],
}

impl<'a> StackAnalyzer<'a> {
    pub fn new(instructions: &'a [DecodedInstruction]) -> Self {
        Self { instructions }
    }

    /// Run stack depth verification against the given budgets.
    ///
    /// `min_gas_decrement` is the smallest `sub x23, x23, #N` amount found
    /// in the program (computed by the caller during gas-check verification).
    /// It bounds loop iterations: `max_iterations = gas_budget / min_gas_decrement`.
    /// Computes a worst-case stack bound that accounts for SP decrements
    /// inside loops being executed multiple times (bounded by gas budget).
    pub fn verify(
        &self,
        stack_budget: u32,
        gas_budget: u64,
        min_gas_decrement: u32,
    ) -> (Vec<VerificationError>, u64) {
        if self.instructions.is_empty() {
            return (vec![], 0);
        }

        let mut errors = Vec::new();

        // Collect [target, offset] ranges from backward branches.
        // Same principle as gas.rs: target <= offset means backward branch,
        // and any cycle must contain at least one.
        let loop_ranges: Vec<std::ops::RangeInclusive<usize>> = self
            .instructions
            .iter()
            .filter(|i| i.is_branch() && !i.is_indirect() && !i.is_call())
            .filter_map(|i| {
                let target = i.branch_target()?;
                (target <= i.offset).then_some(target..=i.offset)
            })
            .collect();

        // Classify each instruction's SP effect.
        let mut non_loop_sp = 0u32;
        let mut loop_sp = 0u32;

        for instruction in self.instructions.iter() {
            match SpEffect::from(instruction) {
                SpEffect::Decrement(n) => {
                    let in_loop = loop_ranges.iter().any(|r| r.contains(&instruction.offset));
                    if in_loop {
                        loop_sp = loop_sp.saturating_add(n);
                    } else {
                        non_loop_sp = non_loop_sp.saturating_add(n);
                    }
                }
                SpEffect::Unsafe => {
                    errors.push(VerificationError::UnsafeStackModification {
                        offset: instruction.offset,
                        mnemonic: instruction.mnemonic().to_string(),
                    });
                }
                _ => {}
            }
        }

        let worst_case = if loop_sp > 0 && min_gas_decrement > 0 {
            let max_iterations = gas_budget / min_gas_decrement as u64;
            non_loop_sp as u64 + loop_sp as u64 * max_iterations
        } else {
            non_loop_sp as u64
        };

        if worst_case > stack_budget as u64 {
            errors.push(VerificationError::StackDepthExceeded {
                max_depth: worst_case,
                budget: stack_budget as u64,
            });
        }

        (errors, worst_case)
    }
}

#[cfg(test)]
mod tests {
    use crate::decode::decode_instructions_unchecked as decode;
    use crate::error::VerificationError;
    use crate::gas::DEFAULT_GAS_BUDGET;

    use super::{DEFAULT_STACK_BUDGET, SpEffect, StackAnalyzer};

    #[test]
    fn test_sp_effect_sub_sp_imm() {
        // sub sp, sp, #32
        let code = [0xff, 0x83, 0x00, 0xd1];
        let instructions = decode(&code);
        assert_eq!(SpEffect::from(&instructions[0]), SpEffect::Decrement(32));
    }

    #[test]
    fn test_sp_effect_stp_preindex() {
        // stp x29, x30, [sp, #-16]!
        let code = [0xfd, 0x7b, 0xbf, 0xa9];
        let instructions = decode(&code);
        assert_eq!(SpEffect::from(&instructions[0]), SpEffect::Decrement(16));
    }

    #[test]
    fn test_sp_effect_str_preindex() {
        // str x0, [sp, #-16]!
        let code = [0xe0, 0x0f, 0x1f, 0xf8];
        let instructions = decode(&code);
        assert_eq!(SpEffect::from(&instructions[0]), SpEffect::Decrement(16));
    }

    #[test]
    fn test_sp_effect_add_sp_imm() {
        // add sp, sp, #32
        let code = [0xff, 0x83, 0x00, 0x91];
        let instructions = decode(&code);
        assert_eq!(SpEffect::from(&instructions[0]), SpEffect::Increment);
    }

    #[test]
    fn test_sp_effect_ldp_postindex() {
        // ldp x29, x30, [sp], #16
        let code = [0xfd, 0x7b, 0xc1, 0xa8];
        let instructions = decode(&code);
        assert_eq!(SpEffect::from(&instructions[0]), SpEffect::Increment);
    }

    #[test]
    fn test_sp_effect_ldr_postindex() {
        // ldr x0, [sp], #16 — post-index load (stack deallocation)
        let code: [u8; 4] = 0xf84107e0_u32.to_le_bytes();
        let instructions = decode(&code);
        assert_eq!(SpEffect::from(&instructions[0]), SpEffect::Increment);
    }

    #[test]
    fn test_sp_effect_non_sp_instruction() {
        // add x0, x1, x2
        let code = [0x20, 0x00, 0x02, 0x8b];
        let instructions = decode(&code);
        assert_eq!(SpEffect::from(&instructions[0]), SpEffect::None);
    }

    #[test]
    fn test_sp_effect_ldr_no_writeback() {
        // ldr x0, [sp, #16] (no writeback) — reads from SP but doesn't modify it
        let code = [0xe0, 0x13, 0x40, 0xf9];
        let instructions = decode(&code);
        assert_eq!(SpEffect::from(&instructions[0]), SpEffect::None);
    }

    #[test]
    fn test_sp_effect_cmp_sp() {
        // cmp sp, #0 — reads SP but doesn't modify it
        let code = [0x1f, 0x00, 0x00, 0xf1];
        let instructions = decode(&code);
        assert_eq!(SpEffect::from(&instructions[0]), SpEffect::None);
    }

    #[test]
    fn test_sp_effect_sub_register_is_unsafe() {
        // sub sp, sp, x0, uxtx — register-based, amount unknown
        let code = [0xff, 0x63, 0x20, 0xcb];
        let instructions = decode(&code);
        assert_eq!(
            SpEffect::from(&instructions[0]),
            SpEffect::Unsafe,
            "sub sp, sp, x0 should be Unsafe (unknown stack decrement)"
        );
    }

    #[test]
    fn test_sp_effect_mov_sp_is_unsafe() {
        // mov sp, x0 → add sp, x0, #0
        let code = [0x1f, 0x00, 0x00, 0x91];
        let instructions = decode(&code);
        assert_eq!(SpEffect::from(&instructions[0]), SpEffect::Unsafe);
    }

    #[test]
    fn test_sp_effect_ldp_negative_postindex_is_unsafe() {
        // ldp x0, x1, [sp], #-16 — decrements SP via post-index
        let code: [u8; 4] = 0xa8ff07e0_u32.to_le_bytes();
        let instructions = decode(&code);
        assert_eq!(SpEffect::from(&instructions[0]), SpEffect::Unsafe);
    }

    #[test]
    fn test_sp_effect_ldr_negative_postindex_is_unsafe() {
        // ldr x0, [sp], #-16 — decrements SP via post-index
        let code: [u8; 4] = 0xf85f07e0_u32.to_le_bytes();
        let instructions = decode(&code);
        assert_eq!(SpEffect::from(&instructions[0]), SpEffect::Unsafe);
    }

    #[test]
    fn test_sp_effect_stp_positive_preindex_is_unsafe() {
        // stp x0, x1, [sp, #16]! — increments SP via pre-index
        let code: [u8; 4] = 0xa98107e0_u32.to_le_bytes();
        let instructions = decode(&code);
        assert_eq!(SpEffect::from(&instructions[0]), SpEffect::Unsafe);
    }

    #[test]
    fn test_sp_effect_str_positive_preindex_is_unsafe() {
        // str x0, [sp, #16]! — increments SP via pre-index
        let code: [u8; 4] = 0xf8010fe0_u32.to_le_bytes();
        let instructions = decode(&code);
        assert_eq!(SpEffect::from(&instructions[0]), SpEffect::Unsafe);
    }

    /// Helper: assert verify() produces no errors.
    fn assert_ok(analyzer: &StackAnalyzer, budget: u32, gas_budget: u64, min_gas: u32) {
        let (errors, _) = analyzer.verify(budget, gas_budget, min_gas);
        assert!(errors.is_empty(), "expected no errors, got: {:?}", errors);
    }

    /// Helper: assert verify() produces an error matching the predicate.
    fn assert_has_error(
        analyzer: &StackAnalyzer,
        budget: u32,
        gas_budget: u64,
        min_gas: u32,
        pred: fn(&VerificationError) -> bool,
        msg: &str,
    ) {
        let (errors, _) = analyzer.verify(budget, gas_budget, min_gas);
        assert!(errors.iter().any(pred), "{}: {:?}", msg, errors);
    }

    #[test]
    fn test_empty_code() {
        let instructions = decode(&[]);
        let analyzer = StackAnalyzer::new(&instructions);
        assert_ok(&analyzer, DEFAULT_STACK_BUDGET, DEFAULT_GAS_BUDGET, 0);
    }

    #[test]
    fn test_budget_exceeded() {
        // Single function with large frame (no loops, so min_gas_decrement irrelevant)
        // sub sp, sp, #4095 (max 12-bit immediate)
        let code = [
            0xff, 0xff, 0x3f, 0xd1, // sub sp, sp, #4095   [0]
            0xff, 0xff, 0x3f, 0x91, // add sp, sp, #4095   [4]
            0xc0, 0x03, 0x5f, 0xd6, // ret                  [8]
        ];
        let instructions = decode(&code);
        let analyzer = StackAnalyzer::new(&instructions);
        let (errors, depth) = analyzer.verify(8, DEFAULT_GAS_BUDGET, 0);
        assert_eq!(depth, 4095);
        assert!(
            errors.iter().any(|e| matches!(
                e,
                VerificationError::StackDepthExceeded {
                    max_depth: 4095,
                    budget: 8
                }
            )),
            "should report stack depth exceeded: {:?}",
            errors
        );
    }

    #[test]
    fn test_linear_sum_across_functions() {
        // Two functions: func1 (frame=16), func2 (frame=32)
        // No loops, so linear sum = 16 + 32 = 48
        let code = [
            0xff, 0x43, 0x00, 0xd1, // sub sp, sp, #16    (offset 0)
            0x03, 0x00, 0x00, 0x94, // bl #12 (offset 16)  (offset 4)
            0xff, 0x43, 0x00, 0x91, // add sp, sp, #16    (offset 8)
            0xc0, 0x03, 0x5f, 0xd6, // ret                (offset 12)
            0xff, 0x83, 0x00, 0xd1, // sub sp, sp, #32    (offset 16) <- func2
            0xff, 0x83, 0x00, 0x91, // add sp, sp, #32    (offset 20)
            0xc0, 0x03, 0x5f, 0xd6, // ret                (offset 24)
        ];
        let instructions = decode(&code);
        let analyzer = StackAnalyzer::new(&instructions);

        // Budget of 47 should fail (linear sum = 16 + 32 = 48)
        let (errors, depth) = analyzer.verify(47, DEFAULT_GAS_BUDGET, 0);
        assert_eq!(depth, 48);
        assert!(
            errors.iter().any(|e| matches!(
                e,
                VerificationError::StackDepthExceeded {
                    max_depth: 48,
                    budget: 47
                }
            )),
            "linear sum should be 48: {:?}",
            errors
        );

        // Budget of 48 should pass
        assert_ok(&analyzer, 48, DEFAULT_GAS_BUDGET, 0);
    }

    #[test]
    fn test_no_frame_passes() {
        // mov x0, #0; ret — no SP modifications at all
        let code = [
            0x00, 0x00, 0x80, 0xd2, // mov x0, #0
            0xc0, 0x03, 0x5f, 0xd6, // ret
        ];
        let instructions = decode(&code);
        let analyzer = StackAnalyzer::new(&instructions);
        assert_ok(&analyzer, DEFAULT_STACK_BUDGET, DEFAULT_GAS_BUDGET, 0);
    }

    #[test]
    fn test_sp_in_loop_exceeds_budget() {
        // Gas-instrumented loop with sub sp, sp, #16 inside.
        // Assembled from:
        //   sub sp, sp, #16; add sp, sp, #16; sub x23, x23, #3;
        //   tbz x23, #63, Lok; brk #0; Lok: b.lt start; ret
        let code = [
            0xff, 0x43, 0x00, 0xd1, // sub sp, sp, #16      [0x00]
            0xff, 0x43, 0x00, 0x91, // add sp, sp, #16      [0x04]
            0xf7, 0x0e, 0x00, 0xd1, // sub x23, x23, #3     [0x08]
            0x57, 0x00, 0xf8, 0xb6, // tbz x23, #63, 0x14   [0x0c]
            0x00, 0x00, 0x20, 0xd4, // brk #0                [0x10]
            0x6b, 0xff, 0xff, 0x54, // b.lt 0x0              [0x14]
            0xc0, 0x03, 0x5f, 0xd6, // ret                   [0x18]
        ];
        let instructions = decode(&code);
        let analyzer = StackAnalyzer::new(&instructions);

        // With gas_budget=300 and min_gas_decrement=3, max_iterations=100
        // worst_case = 0 (non-loop) + 16 (loop_sp) * 100 = 1600
        // A small stack budget should fail
        assert_has_error(
            &analyzer,
            64,
            300,
            3,
            |e| matches!(e, VerificationError::StackDepthExceeded { .. }),
            "SP decrement in loop should exceed budget",
        );

        // Large budget should pass
        assert_ok(&analyzer, 2000, 300, 3);
    }

    #[test]
    fn test_loop_sp_ignored_when_no_gas_decrement() {
        // Same loop code as test_sp_in_loop_exceeds_budget, but with
        // min_gas_decrement=0 (caller found no gas decrements).
        // verify() should treat worst_case = non_loop_sp only (loop SP ignored).
        let code = [
            0xff, 0x43, 0x00, 0xd1, // sub sp, sp, #16      [0x00]
            0xff, 0x43, 0x00, 0x91, // add sp, sp, #16      [0x04]
            0xf7, 0x0e, 0x00, 0xd1, // sub x23, x23, #3     [0x08]
            0x57, 0x00, 0xf8, 0xb6, // tbz x23, #63, 0x14   [0x0c]
            0x00, 0x00, 0x20, 0xd4, // brk #0                [0x10]
            0x6b, 0xff, 0xff, 0x54, // b.lt 0x0              [0x14]
            0xc0, 0x03, 0x5f, 0xd6, // ret                   [0x18]
        ];
        let instructions = decode(&code);
        let analyzer = StackAnalyzer::new(&instructions);

        // min_gas_decrement=0 → loop SP ignored, worst_case = 0 (no non-loop SP)
        assert_ok(&analyzer, 1, 300, 0);
    }

    #[test]
    fn test_sp_in_prologue_not_in_loop() {
        // SP decrement in function prologue (not a loop), then a gas-instrumented loop
        // with no SP decrements. The prologue SP should NOT be multiplied.
        // Assembled from:
        //   sub sp, sp, #32; Lloop: add x0, x0, #1; sub x23, x23, #2;
        //   tbz x23, #63, Lok; brk #0; Lok: b.lt Lloop; add sp, sp, #32; ret
        let code = [
            0xff, 0x83, 0x00, 0xd1, // sub sp, sp, #32      [0x00]
            0x00, 0x04, 0x00, 0x91, // add x0, x0, #1       [0x04]
            0xf7, 0x0a, 0x00, 0xd1, // sub x23, x23, #2     [0x08]
            0x57, 0x00, 0xf8, 0xb6, // tbz x23, #63, 0x14   [0x0c]
            0x00, 0x00, 0x20, 0xd4, // brk #0                [0x10]
            0x8b, 0xff, 0xff, 0x54, // b.lt 0x04             [0x14]
            0xff, 0x83, 0x00, 0x91, // add sp, sp, #32      [0x18]
            0xc0, 0x03, 0x5f, 0xd6, // ret                   [0x1c]
        ];
        let instructions = decode(&code);
        let analyzer = StackAnalyzer::new(&instructions);

        // Non-loop SP = 32, loop SP = 0 -> worst_case = 32
        // Budget of 32 should be enough (min_gas_decrement irrelevant since loop_sp=0)
        assert_ok(&analyzer, 32, DEFAULT_GAS_BUDGET, 2);
    }

    #[test]
    fn test_unsafe_sp_detected() {
        // sub sp, sp, x0, uxtx — register-based SP modification
        let code = [0xff, 0x63, 0x20, 0xcb];
        let instructions = decode(&code);
        let analyzer = StackAnalyzer::new(&instructions);
        assert_has_error(
            &analyzer,
            DEFAULT_STACK_BUDGET,
            DEFAULT_GAS_BUDGET,
            0,
            |e| matches!(e, VerificationError::UnsafeStackModification { .. }),
            "sub sp, sp, x0 should produce UnsafeStackModification",
        );
    }
}
