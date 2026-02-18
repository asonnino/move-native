// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Arm64 instruction decoding
//!
//! Decodes raw bytes into structured Arm64 instructions using the `yaxpeax-arm` crate.

use cfg::{BasicInstruction, CfgInstruction, CheckResult, ClassifiedOpcode};
use yaxpeax_arch::{Decoder, U8Reader};
use yaxpeax_arm::armv8::a64::{InstDecoder, Instruction, Opcode, Operand};

use crate::error::DecodeError;

/// A decoded instruction with its location information
#[derive(Debug)]
pub struct DecodedInstruction {
    /// Offset from start of code section (in bytes)
    pub offset: usize,
    /// The raw 32-bit instruction word
    pub raw: u32,
    /// The decoded instruction
    pub instruction: Instruction,
    /// Mnemonic string (for InstructionInfo trait)
    mnemonic: String,
}

impl DecodedInstruction {
    /// Returns the opcode of this instruction
    pub fn opcode(&self) -> Opcode {
        self.instruction.opcode
    }

    /// Returns the operands of this instruction
    pub fn operands(&self) -> &[Operand; 4] {
        &self.instruction.operands
    }

    /// Check if this instruction is allowed in deterministic code
    pub fn check(&self) -> CheckResult {
        ClassifiedOpcode::from_opcode(self.opcode()).check_result
    }

    /// Check if this is a store instruction (operand[0] is value, not destination)
    pub fn is_store(&self) -> bool {
        ClassifiedOpcode::from_opcode(self.opcode()).is_store
    }

    /// Check if this is a `bl` (branch with link) instruction.
    pub fn is_bl(&self) -> bool {
        self.opcode() == Opcode::BL
    }

    /// Check if this is `brk #0` (out-of-gas trap)
    pub fn is_brk_trap(&self) -> bool {
        if self.opcode() != Opcode::BRK {
            return false;
        }

        matches!(
            &self.operands()[0],
            Operand::Immediate(0) | Operand::Imm16(0)
        )
    }
}

/// Implementation of BasicInstruction for mnemonic-based classification.
impl BasicInstruction for DecodedInstruction {
    fn mnemonic(&self) -> &str {
        &self.mnemonic
    }
}

/// Implementation of CfgInstruction for generic CFG building.
impl CfgInstruction for DecodedInstruction {
    fn branch_target(&self) -> Option<usize> {
        // Indirect branches (BR, BLR, RET, etc.) have register targets
        if self.is_branch() && self.is_indirect() {
            return None;
        }

        // Look for PC-relative offset in operands
        for op in self.operands() {
            if let Operand::PCOffset(offset) = op {
                let target = self.offset as i64 + offset;
                return usize::try_from(target).ok();
            }
        }
        None
    }

    fn as_target(&self) -> usize {
        self.offset
    }
}

/// Decode all instructions from a byte slice
///
/// The input must be 4-byte aligned (Arm64 fixed-width instructions).
/// Returns a vector of decoded instructions.
pub fn decode_instructions(code: &[u8]) -> Result<Vec<DecodedInstruction>, DecodeError> {
    if !code.len().is_multiple_of(4) {
        return Err(DecodeError::UnalignedCode { size: code.len() });
    }

    let decoder = InstDecoder::default();
    let mut instructions = Vec::with_capacity(code.len() / 4);

    for (i, chunk) in code.chunks_exact(4).enumerate() {
        let offset = i * 4;
        let raw = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);

        let mut reader = U8Reader::new(chunk);
        let instruction =
            decoder
                .decode(&mut reader)
                .map_err(|e| DecodeError::InvalidInstruction {
                    offset,
                    message: format!("{:?}", e),
                })?;

        let mnemonic = instruction.opcode.to_string();
        instructions.push(DecodedInstruction {
            offset,
            raw,
            instruction,
            mnemonic,
        });
    }

    Ok(instructions)
}

/// Test-only wrapper that panics on decode failure.
#[cfg(test)]
pub(crate) fn decode_instructions_unchecked(code: &[u8]) -> Vec<DecodedInstruction> {
    decode_instructions(code).expect("decode failed")
}

#[cfg(test)]
mod tests {
    use cfg::{BasicInstruction, CfgInstruction};
    use yaxpeax_arm::armv8::a64::Opcode;

    use super::decode_instructions_unchecked as decode;
    use crate::DecodeError;

    #[test]
    fn test_decode_nop() {
        // NOP is encoded as 0xd503201f
        let code = [0x1f, 0x20, 0x03, 0xd5];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert_eq!(instructions[0].opcode(), Opcode::HINT);
        assert_eq!(instructions[0].offset, 0);
    }

    #[test]
    fn test_decode_branch() {
        // B #0x10 (branch forward 16 bytes) is encoded as 0x14000004
        let code = [0x04, 0x00, 0x00, 0x14];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        let instr = &instructions[0];
        assert!(instr.is_branch());
        assert!(!instr.is_conditional()); // unconditional
        assert!(!instr.is_indirect()); // direct branch
        assert_eq!(instr.branch_target(), Some(16));
    }

    #[test]
    fn test_decode_conditional_branch() {
        // B.LT #-8 (branch back 8 bytes if less than)
        let code = [0x4b, 0xff, 0xff, 0x54]; // b.lt #-8
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        let instr = &instructions[0];
        assert!(instr.is_branch());
        assert!(instr.is_conditional());
    }

    #[test]
    fn test_decode_ret() {
        // RET is encoded as 0xd65f03c0
        let code = [0xc0, 0x03, 0x5f, 0xd6];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        let instr = &instructions[0];
        assert_eq!(instr.opcode(), Opcode::RET);
        assert!(instr.is_branch());
        assert!(instr.is_indirect()); // RET is register-indirect
    }

    #[test]
    fn test_decode_brk() {
        // brk #0 -> 0xd4200000
        let code = [0x00, 0x00, 0x20, 0xd4];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert_eq!(instructions[0].opcode(), Opcode::BRK);
        assert!(instructions[0].is_brk_trap());
    }

    #[test]
    fn test_unaligned_code_error() {
        let code = [0x1f, 0x20, 0x03]; // 3 bytes - not aligned
        let result = crate::decode_instructions(&code);

        assert!(result.is_err());
        assert!(matches!(result, Err(DecodeError::UnalignedCode { .. })));
    }

    #[test]
    fn test_multiple_instructions() {
        // mov x0, #0 -> 0xd2800000
        // mov x1, #1 -> 0xd2800021
        // add x0, x0, x1 -> 0x8b010000
        // ret -> 0xd65f03c0
        let code = [
            0x00, 0x00, 0x80, 0xd2, // mov x0, #0
            0x21, 0x00, 0x80, 0xd2, // mov x1, #1
            0x00, 0x00, 0x01, 0x8b, // add x0, x0, x1
            0xc0, 0x03, 0x5f, 0xd6, // ret
        ];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 4);
        assert_eq!(instructions[0].offset, 0);
        assert_eq!(instructions[1].offset, 4);
        assert_eq!(instructions[2].offset, 8);
        assert_eq!(instructions[3].offset, 12);
    }

    #[test]
    fn test_detect_indirect_branch_br() {
        // br x0 -> 0xd61f0000
        // Malicious: could jump anywhere
        let code = [0x00, 0x00, 0x1f, 0xd6];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        let instr = &instructions[0];
        assert_eq!(instr.opcode(), Opcode::BR);
        assert!(instr.is_branch());
        assert!(instr.is_indirect());
    }

    #[test]
    fn test_detect_indirect_branch_blr() {
        // blr x8 -> 0xd63f0100
        // Malicious: could call anywhere
        let code = [0x00, 0x01, 0x3f, 0xd6];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        let instr = &instructions[0];
        assert_eq!(instr.opcode(), Opcode::BLR);
        assert!(instr.is_branch());
        assert!(instr.is_indirect());
    }

    #[test]
    fn test_detect_pac_indirect_branch_braaz() {
        // braaz x0 -> 0xd61f081f (Armv8.3-A PAC branch)
        // Malicious: PAC-authenticated indirect branch
        let code = [0x1f, 0x08, 0x1f, 0xd6];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        let instr = &instructions[0];
        assert_eq!(instr.opcode(), Opcode::BRAAZ);
        assert!(instr.is_branch());
        assert!(instr.is_indirect());
    }

    #[test]
    fn test_detect_pac_indirect_branch_retaa() {
        // retaa -> 0xd65f0bff (Armv8.3-A PAC return)
        // Malicious: PAC-authenticated return
        let code = [0xff, 0x0b, 0x5f, 0xd6];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        let instr = &instructions[0];
        assert_eq!(instr.opcode(), Opcode::RETAA);
        assert!(instr.is_branch());
        assert!(instr.is_indirect());
    }

    #[test]
    fn test_is_bl() {
        // bl #8 -> 0x94000002
        let code = [0x02, 0x00, 0x00, 0x94];
        let instructions = crate::decode_instructions(&code).unwrap();
        assert!(instructions[0].is_bl());
    }

    #[test]
    fn test_branch_target_negative_underflow() {
        // b #-4 at offset 0: target = 0 + (-4) = -4 → None (can't represent as usize)
        let code = [0xff, 0xff, 0xff, 0x17]; // b #-4
        let instructions = decode(&code);

        assert!(instructions[0].is_branch());
        assert_eq!(
            instructions[0].branch_target(),
            None,
            "negative target should return None"
        );
    }

    #[test]
    fn test_check_and_is_store_methods() {
        use cfg::CheckResult;

        // str x0, [sp] — allowed store
        let code = [0xe0, 0x03, 0x00, 0xf9];
        let instructions = decode(&code);
        assert_eq!(instructions[0].check(), CheckResult::Allowed);
        assert!(instructions[0].is_store());

        // add x0, x0, #1 — allowed non-store
        let code = [0x00, 0x04, 0x00, 0x91];
        let instructions = decode(&code);
        assert_eq!(instructions[0].check(), CheckResult::Allowed);
        assert!(!instructions[0].is_store());

        // ldxr x0, [x1] — rejected (Atomic)
        let code = [0x20, 0x7c, 0x5f, 0xc8];
        let instructions = decode(&code);
        assert!(matches!(instructions[0].check(), CheckResult::Rejected(_)));
        assert!(!instructions[0].is_store());
    }

    #[test]
    fn test_brk_nonzero_not_trap() {
        // brk #1 -> 0xd4200020 — only brk #0 is our gas trap
        let code = [0x20, 0x00, 0x20, 0xd4];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions[0].opcode(), Opcode::BRK);
        assert!(
            !instructions[0].is_brk_trap(),
            "brk #1 should not be recognized as gas trap"
        );
    }
}
