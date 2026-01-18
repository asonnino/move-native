//! Arm64 instruction decoding
//!
//! Decodes raw bytes into structured Arm64 instructions using the `yaxpeax-arm` crate.

use cfg::{CheckResult, ClassifiedOpcode, InstructionInfo};
use thiserror::Error;
use yaxpeax_arch::{Decoder, U8Reader};
use yaxpeax_arm::armv8::a64::{InstDecoder, Instruction, Opcode, Operand, SizeCode};

/// Check if an operand is x23 (either as Register or RegisterOrSP)
fn is_x23(op: &Operand) -> bool {
    matches!(
        op,
        Operand::Register(SizeCode::X, 23) | Operand::RegisterOrSP(SizeCode::X, 23)
    )
}

/// Errors that can occur during decoding
#[derive(Debug, Error)]
pub enum DecodeError {
    #[error("failed to decode instruction at offset {offset:#x}: {message}")]
    InvalidInstruction { offset: usize, message: String },

    #[error("code section size {size} is not aligned to 4 bytes (corrupted binary?)")]
    UnalignedCode { size: usize },
}

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

    /// Check if this instruction is a branch (conditional or unconditional)
    ///
    /// Uses cfg for consistent classification across crates.
    pub fn is_branch(&self) -> bool {
        ClassifiedOpcode::from_opcode(self.opcode()).is_branch
    }

    /// Check if this is an unconditional direct branch (B or BL)
    pub fn is_unconditional_branch(&self) -> bool {
        let c = ClassifiedOpcode::from_opcode(self.opcode());
        c.is_branch && !c.is_conditional && !c.is_indirect
    }

    /// Check if this is a conditional branch
    pub fn is_conditional_branch(&self) -> bool {
        let c = ClassifiedOpcode::from_opcode(self.opcode());
        c.is_branch && c.is_conditional
    }

    /// Check if this is an indirect branch (BR, BLR, RET, ERET and PAC variants)
    ///
    /// These are forbidden in Move-compiled code since Move has no dynamic dispatch.
    /// Indirect branches could jump to uninstrumented code.
    pub fn is_indirect_branch(&self) -> bool {
        let c = ClassifiedOpcode::from_opcode(self.opcode());
        c.is_branch && c.is_indirect
    }

    /// Get the branch target offset (for direct branches), relative to this instruction
    pub fn branch_target_offset(&self) -> Option<i64> {
        if self.is_indirect_branch() {
            return None;
        }

        for op in self.operands() {
            if let Operand::PCOffset(offset) = op {
                return Some(*offset);
            }
        }
        None
    }

    /// Get the absolute branch target address (for direct branches)
    pub fn branch_target(&self) -> Option<usize> {
        self.branch_target_offset().map(|offset| {
            let target = self.offset as i64 + offset;
            target as usize
        })
    }

    /// Check if this instruction writes to register x23 (gas register)
    pub fn writes_to_x23(&self) -> bool {
        // First operand is typically the destination for most instructions
        if is_x23(&self.operands()[0]) {
            // Check if this is a write operation (exclude compares and branches)
            // Note: CMP/CMN are aliases for SUBS/ADDS with xzr destination, so they won't match x23
            !self.is_branch() && !matches!(self.opcode(), Opcode::CCMP | Opcode::CCMN)
        } else {
            false
        }
    }

    /// Check if this is a SUB instruction targeting x23 (gas decrement)
    pub fn is_gas_decrement(&self) -> bool {
        if !matches!(self.opcode(), Opcode::SUB | Opcode::SUBS) {
            return false;
        }

        let ops = self.operands();

        // Check: sub x23, x23, #imm
        is_x23(&ops[0]) && is_x23(&ops[1])
    }

    /// Get the immediate value from a gas decrement instruction
    pub fn gas_decrement_amount(&self) -> Option<u32> {
        if !self.is_gas_decrement() {
            return None;
        }

        match &self.operands()[2] {
            Operand::Immediate(imm) => Some(*imm),
            Operand::Imm64(imm) => Some(*imm as u32),
            _ => None,
        }
    }

    /// Check if this is `tbz x23, #63, <label>` (gas check branch)
    pub fn is_gas_check_branch(&self) -> bool {
        if self.opcode() != Opcode::TBZ {
            return false;
        }

        let ops = self.operands();

        // Check: tbz x23, #63, ...
        let is_bit_63 = matches!(&ops[1], Operand::Immediate(63) | Operand::Imm16(63));

        is_x23(&ops[0]) && is_bit_63
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

/// Implementation of InstructionInfo for generic CFG building.
///
/// For binary instructions:
/// - Position is byte offset
/// - Target is byte offset (for branch targets)
/// - No labels (binary doesn't have symbolic labels)
impl InstructionInfo for DecodedInstruction {
    type Position = usize;
    type Target = usize;

    fn position(&self) -> usize {
        self.offset
    }

    fn mnemonic(&self) -> Option<&str> {
        Some(&self.mnemonic)
    }

    fn branch_target(&self) -> Option<usize> {
        self.branch_target_offset().map(|offset| {
            let target = self.offset as i64 + offset;
            target as usize
        })
    }

    fn label(&self) -> Option<usize> {
        // Binary doesn't have symbolic labels
        None
    }

    fn position_as_target(&self) -> Option<usize> {
        // Binary uses position comparison to identify branch targets
        Some(self.offset)
    }
}

/// Decode all instructions from a byte slice
///
/// The input must be 4-byte aligned (Arm64 fixed-width instructions).
/// Returns a vector of decoded instructions.
pub fn decode_instructions(code: &[u8]) -> Result<Vec<DecodedInstruction>, DecodeError> {
    if code.len() % 4 != 0 {
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

#[cfg(test)]
mod tests {
    use yaxpeax_arm::armv8::a64::Opcode;

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
        assert!(instructions[0].is_branch());
        assert!(instructions[0].is_unconditional_branch());
        assert!(!instructions[0].is_indirect_branch());
        assert_eq!(instructions[0].branch_target(), Some(16));
    }

    #[test]
    fn test_decode_conditional_branch() {
        // B.LT #-8 (branch back 8 bytes if less than)
        let code = [0x4b, 0xff, 0xff, 0x54]; // b.lt #-8
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert!(instructions[0].is_branch());
        assert!(instructions[0].is_conditional_branch());
    }

    #[test]
    fn test_decode_ret() {
        // RET is encoded as 0xd65f03c0
        let code = [0xc0, 0x03, 0x5f, 0xd6];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert_eq!(instructions[0].opcode(), Opcode::RET);
        assert!(instructions[0].is_branch());
        assert!(instructions[0].is_indirect_branch());
    }

    #[test]
    fn test_decode_sub_x23() {
        // sub x23, x23, #3 -> 0xd10012f7
        let code = [0xf7, 0x0e, 0x00, 0xd1];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert!(instructions[0].is_gas_decrement());
        assert_eq!(instructions[0].gas_decrement_amount(), Some(3));
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
    fn test_detect_x23_tampering_mov() {
        // mov x23, #1 -> 0xd2800037 (MOVZ x23, #1)
        // Malicious: sets gas register to arbitrary value
        let code = [0x37, 0x00, 0x80, 0xd2];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert!(instructions[0].writes_to_x23(), "should detect x23 write");
        assert!(
            !instructions[0].is_gas_decrement(),
            "mov should not be gas decrement"
        );
    }

    #[test]
    fn test_detect_x23_tampering_add() {
        // add x23, x23, #1 -> 0x910006f7
        // Malicious: increments gas (should only decrement)
        let code = [0xf7, 0x06, 0x00, 0x91];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert!(instructions[0].writes_to_x23(), "should detect x23 write");
        assert!(
            !instructions[0].is_gas_decrement(),
            "add should not be gas decrement"
        );
    }

    #[test]
    fn test_detect_indirect_branch_br() {
        // br x0 -> 0xd61f0000
        // Malicious: could jump anywhere
        let code = [0x00, 0x00, 0x1f, 0xd6];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert_eq!(instructions[0].opcode(), Opcode::BR);
        assert!(instructions[0].is_indirect_branch());
        assert!(instructions[0].is_branch());
    }

    #[test]
    fn test_detect_indirect_branch_blr() {
        // blr x8 -> 0xd63f0100
        // Malicious: could call anywhere
        let code = [0x00, 0x01, 0x3f, 0xd6];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert_eq!(instructions[0].opcode(), Opcode::BLR);
        assert!(instructions[0].is_indirect_branch());
        assert!(instructions[0].is_branch());
    }

    #[test]
    fn test_gas_check_branch_tbz() {
        // tbz x23, #63, #8 -> 0xb6f80097
        // This is the valid gas check: branch if bit 63 is zero (positive)
        let code = [0x97, 0x00, 0xf8, 0xb6];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert!(instructions[0].is_gas_check_branch());
        assert!(instructions[0].is_branch());
        assert!(!instructions[0].is_indirect_branch());
    }

    #[test]
    fn test_legitimate_gas_decrement() {
        // sub x23, x23, #5 -> 0xd10016f7
        // This is the valid gas decrement pattern
        let code = [0xf7, 0x16, 0x00, 0xd1];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert!(instructions[0].is_gas_decrement());
        assert!(instructions[0].writes_to_x23());
        assert_eq!(instructions[0].gas_decrement_amount(), Some(5));
    }

    #[test]
    fn test_sub_other_register_not_gas_decrement() {
        // sub x0, x0, #3 -> 0xd1000c00
        // Not a gas decrement (wrong register)
        let code = [0x00, 0x0c, 0x00, 0xd1];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert!(!instructions[0].is_gas_decrement());
        assert!(!instructions[0].writes_to_x23());
    }

    #[test]
    fn test_detect_pac_indirect_branch_braaz() {
        // braaz x0 -> 0xd61f081f (Armv8.3-A PAC branch)
        // Malicious: PAC-authenticated indirect branch
        let code = [0x1f, 0x08, 0x1f, 0xd6];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert_eq!(instructions[0].opcode(), Opcode::BRAAZ);
        assert!(instructions[0].is_indirect_branch());
        assert!(instructions[0].is_branch());
    }

    #[test]
    fn test_detect_pac_indirect_branch_retaa() {
        // retaa -> 0xd65f0bff (Armv8.3-A PAC return)
        // Malicious: PAC-authenticated return
        let code = [0xff, 0x0b, 0x5f, 0xd6];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert_eq!(instructions[0].opcode(), Opcode::RETAA);
        assert!(instructions[0].is_indirect_branch());
        assert!(instructions[0].is_branch());
    }
}
