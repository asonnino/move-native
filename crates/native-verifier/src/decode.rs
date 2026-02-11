//! Arm64 instruction decoding
//!
//! Decodes raw bytes into structured Arm64 instructions using the `yaxpeax-arm` crate.

use cfg::{BasicInstruction, CfgInstruction, CheckResult, ClassifiedOpcode};
use yaxpeax_arch::{Decoder, U8Reader};
use yaxpeax_arm::armv8::a64::{InstDecoder, Instruction, Opcode, Operand, SizeCode};

use crate::error::VerificationError;

/// Errors that can occur during decoding
#[derive(Debug, thiserror::Error)]
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

    /// Check if an operand is x23/w23 as destination (either as Register or RegisterOrSP)
    ///
    /// Includes w23 (32-bit alias) because writing to w23 clears x23's upper bits,
    /// which could bypass gas checks by clearing the sign bit.
    fn is_x23_destination(op: &Operand) -> bool {
        matches!(
            op,
            Operand::Register(SizeCode::X, 23)
                | Operand::Register(SizeCode::W, 23)
                | Operand::RegisterOrSP(SizeCode::X, 23)
                | Operand::RegisterOrSP(SizeCode::W, 23)
        )
    }

    /// Check if an operand references x23/w23 in any position (source, destination, base, index)
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

            // Register with shift (e.g., x23, lsl #3 in add x0, x1, x23, lsl #3) - both sizes
            Operand::RegShift(_, _, SizeCode::X, 23) | Operand::RegShift(_, _, SizeCode::W, 23) => {
                true
            }

            // Memory addressing - x23 as base (all forms)
            // Note: base register is always 64-bit (Xn), but we check reg number
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

    /// Check if this instruction references register x23 (gas register) in any operand
    ///
    /// This is a defense-in-depth measure: we forbid ANY instruction that touches x23,
    /// unless it's the valid gas decrement `sub x23, x23, #N`. This prevents:
    /// - Direct modifications: `mov x23, #1`
    /// - Writeback: `ldr x0, [x23], #8`
    /// - Store to memory: `str x23, [sp]` (could be used to save/restore)
    /// - Use as base: `ldr x0, [x23]` (gas counter shouldn't be used as pointer)
    /// - Use as operand: `add x0, x1, x23` (gas counter shouldn't leak to other regs)
    pub fn touches_x23(&self) -> bool {
        for op in self.operands() {
            if Self::operand_references_x23(op) {
                return true;
            }
        }
        false
    }

    /// Check if this is a SUB instruction targeting x23 (gas decrement)
    ///
    /// Returns true only if this is `sub x23, x23, #N` where N > 0.
    /// A decrement of 0 would allow infinite loops without gas consumption.
    pub fn is_gas_decrement(&self) -> bool {
        if !matches!(self.opcode(), Opcode::SUB | Opcode::SUBS) {
            return false;
        }

        let ops = self.operands();

        // Check: sub x23, x23, #imm
        if !Self::is_x23_destination(&ops[0]) || !Self::is_x23_destination(&ops[1]) {
            return false;
        }

        // Ensure decrement amount > 0
        match &ops[2] {
            Operand::Immediate(i) => *i > 0,
            Operand::Imm64(i) => *i > 0,
            _ => false, // Must be an immediate operand
        }
    }

    #[cfg(test)]
    fn gas_decrement_amount(&self) -> Option<u32> {
        if !self.is_gas_decrement() {
            return None;
        }

        match &self.operands()[2] {
            Operand::Immediate(i) => Some(*i),
            Operand::Imm64(i) => Some(*i as u32),
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

        Self::is_x23_destination(&ops[0]) && is_bit_63
    }

    /// Check if this is a `bl` (branch with link) instruction.
    pub fn is_bl(&self) -> bool {
        self.opcode() == Opcode::BL
    }

    /// Returns the SP decrement amount (in bytes) for recognized
    /// SP-decrementing instructions.
    ///
    /// Recognized patterns:
    /// - `sub sp, sp, #N` — immediate stack allocation
    /// - `stp Xt, Xt2, [sp, #-N]!` — pre-index store pair
    /// - `str Xt, [sp, #-N]!` — pre-index store
    ///
    /// Returns `Ok(0)` for instructions that don't decrement SP.
    /// Returns `Err(UnknownStackDecrement)` if the instruction decrements SP
    /// but the amount can't be statically determined (e.g. `sub sp, sp, x0`).
    pub fn sp_decrement(&self) -> Result<u32, VerificationError> {
        let ops = self.operands();
        match self.opcode() {
            Opcode::SUB => {
                // sub sp, sp, #N: dst=RegisterOrSP(X,31), src=RegisterOrSP(X,31), imm
                let is_sp_dst = matches!(ops[0], Operand::RegisterOrSP(SizeCode::X, 31));
                let is_sp_src = matches!(ops[1], Operand::RegisterOrSP(SizeCode::X, 31));
                if !is_sp_dst || !is_sp_src {
                    return Ok(0);
                }
                match &ops[2] {
                    Operand::Immediate(n) => Ok(*n),
                    Operand::Imm64(n) => Ok(*n as u32),
                    _ => Err(VerificationError::UnknownStackDecrement {
                        offset: self.offset,
                        description: format!("sub sp, sp, {}", self.mnemonic),
                    }),
                }
            }
            Opcode::STP => {
                // stp Xt, Xt2, [sp, #-N]! → operand[2] is RegPreIndex(31, neg_offset, true)
                if let Operand::RegPreIndex(31, offset, true) = &ops[2] {
                    if *offset < 0 {
                        return Ok((-*offset) as u32);
                    }
                }
                Ok(0)
            }
            Opcode::STR => {
                // str Xt, [sp, #-N]! → operand[1] is RegPreIndex(31, neg_offset, true)
                if let Operand::RegPreIndex(31, offset, true) = &ops[1] {
                    if *offset < 0 {
                        return Ok((-*offset) as u32);
                    }
                }
                Ok(0)
            }
            _ => Ok(0),
        }
    }

    /// Check if this instruction modifies SP (register 31 in RegisterOrSP context).
    ///
    /// SP is modified in exactly two ways on ARM64:
    /// 1. Destination operand: RegisterOrSP(_, 31) in operands()[0] for opcodes that
    ///    write to their first operand (excludes comparisons and stores).
    /// 2. Writeback: RegPreIndex(31, ..), RegPostIndex(31, ..), RegPostIndexReg(31, ..)
    fn modifies_sp(&self) -> bool {
        let ops = self.operands();

        // Case 1: SP as destination (first operand).
        // Exclude store opcodes where operands[0] is the value being stored, not a destination.
        // Note: CMP/CMN/TST don't need exclusion — they're aliases for SUBS/ADDS/ANDS
        // with XZR destination, which yaxpeax represents as Register(_, 31) not
        // RegisterOrSP(_, 31), so they won't match the SP check below.
        let is_store = matches!(
            self.opcode(),
            Opcode::STR
                | Opcode::STP
                | Opcode::STRB
                | Opcode::STRH
                | Opcode::STUR
                | Opcode::STURB
                | Opcode::STURH
        );

        if !is_store {
            if matches!(
                ops[0],
                Operand::RegisterOrSP(SizeCode::X, 31) | Operand::RegisterOrSP(SizeCode::W, 31)
            ) {
                return true;
            }
        }

        // Case 2: Writeback addressing modes with SP as base.
        // RegPreIndex(base, offset, writeback): only writeback=true modifies SP.
        // RegPostIndex and RegPostIndexReg always modify the base register.
        for op in ops {
            match op {
                Operand::RegPreIndex(31, _, true)
                | Operand::RegPostIndex(31, _)
                | Operand::RegPostIndexReg(31, _) => return true,
                _ => {}
            }
        }

        false
    }

    /// Check if this is a recognized safe SP modification pattern.
    ///
    /// Recognized patterns (3 decrements + 3 increments):
    /// 1. `sub sp, sp, #N` — allocation
    /// 2. `stp Xt, Xt2, [sp, #-N]!` — pre-index store pair
    /// 3. `str Xt, [sp, #-N]!` — pre-index store
    /// 4. `add sp, sp, #N` — deallocation
    /// 5. `ldp Xt, Xt2, [sp], #N` — post-index load pair
    /// 6. `ldr Xt, [sp], #N` — post-index load
    fn is_recognized_sp_pattern(&self) -> bool {
        let ops = self.operands();
        match self.opcode() {
            // Pattern 1: sub sp, sp, #N
            Opcode::SUB => {
                matches!(ops[0], Operand::RegisterOrSP(SizeCode::X, 31))
                    && matches!(ops[1], Operand::RegisterOrSP(SizeCode::X, 31))
                    && matches!(ops[2], Operand::Immediate(_) | Operand::Imm64(_))
            }
            // Pattern 4: add sp, sp, #N
            Opcode::ADD => {
                matches!(ops[0], Operand::RegisterOrSP(SizeCode::X, 31))
                    && matches!(ops[1], Operand::RegisterOrSP(SizeCode::X, 31))
                    && matches!(ops[2], Operand::Immediate(_) | Operand::Imm64(_))
            }
            // Pattern 2: stp Xt, Xt2, [sp, #-N]!
            // Pattern 5: ldp Xt, Xt2, [sp], #N
            Opcode::STP => matches!(ops[2], Operand::RegPreIndex(31, _, true)),
            Opcode::LDP => matches!(ops[2], Operand::RegPostIndex(31, _)),
            // Pattern 3: str Xt, [sp, #-N]!
            // Pattern 6: ldr Xt, [sp], #N
            Opcode::STR => matches!(ops[1], Operand::RegPreIndex(31, _, true)),
            Opcode::LDR => matches!(ops[1], Operand::RegPostIndex(31, _)),
            _ => false,
        }
    }

    /// Returns true if this instruction modifies SP in a way that isn't one of
    /// the 6 recognized safe patterns. Such instructions make stack depth
    /// unbounded and must be rejected.
    pub fn is_unsafe_sp_modification(&self) -> bool {
        self.modifies_sp() && !self.is_recognized_sp_pattern()
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
    use cfg::{BasicInstruction, CfgInstruction};
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
        assert!(instructions[0].touches_x23(), "should detect x23 usage");
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
        assert!(instructions[0].touches_x23(), "should detect x23 usage");
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
    fn test_gas_check_branch_tbz() {
        // tbz x23, #63, #8 -> 0xb6f80097
        // This is the valid gas check: branch if bit 63 is zero (positive)
        let code = [0x97, 0x00, 0xf8, 0xb6];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        let instr = &instructions[0];
        assert!(instr.is_gas_check_branch());
        assert!(instr.is_branch());
        assert!(!instr.is_indirect()); // TBZ is a direct branch
    }

    #[test]
    fn test_legitimate_gas_decrement() {
        // sub x23, x23, #5 -> 0xd10016f7
        // This is the valid gas decrement pattern
        let code = [0xf7, 0x16, 0x00, 0xd1];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert!(instructions[0].is_gas_decrement());
        assert!(instructions[0].touches_x23());
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
        assert!(!instructions[0].touches_x23());
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

    // Security tests for vulnerability fixes

    #[test]
    fn test_detect_x23_writeback_post_index_load() {
        // ldr x0, [x23], #8 -> 0xf84086e0
        // Malicious: modifies x23 via post-index writeback
        let code = [0xe0, 0x86, 0x40, 0xf8];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert!(
            instructions[0].touches_x23(),
            "should detect x23 usage via post-index load"
        );
    }

    #[test]
    fn test_detect_x23_writeback_post_index_store() {
        // str x0, [x23], #8 -> 0xf80086e0
        // Malicious: modifies x23 via post-index writeback
        let code = [0xe0, 0x86, 0x00, 0xf8];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert!(
            instructions[0].touches_x23(),
            "should detect x23 usage via post-index store"
        );
    }

    #[test]
    fn test_detect_x23_writeback_pre_index() {
        // ldr x0, [x23, #8]! -> 0xf8408ee0
        // Malicious: modifies x23 via pre-index writeback
        let code = [0xe0, 0x8e, 0x40, 0xf8];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert!(
            instructions[0].touches_x23(),
            "should detect x23 usage via pre-index writeback"
        );
    }

    #[test]
    fn test_zero_gas_decrement_rejected() {
        // sub x23, x23, #0 -> 0xd10002f7
        // Malicious: appears to be gas decrement but doesn't actually decrease gas
        let code = [0xf7, 0x02, 0x00, 0xd1];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert!(
            !instructions[0].is_gas_decrement(),
            "sub x23, x23, #0 should NOT be a valid gas decrement"
        );
        assert!(
            instructions[0].touches_x23(),
            "sub x23, x23, #0 should still be detected as x23 usage"
        );
    }

    #[test]
    fn test_x23_as_base_no_writeback() {
        // ldr x0, [x23, #8] (no writeback - no '!') -> 0xf94006e0
        // This doesn't modify x23, but DOES use it as base - should still be flagged
        let code = [0xe0, 0x06, 0x40, 0xf9];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert!(
            instructions[0].touches_x23(),
            "ldr with x23 as base should be detected"
        );
    }

    #[test]
    fn test_x23_as_source_in_store() {
        // str x23, [sp] -> stores x23 to stack
        // This could be used to save/restore x23 to bypass metering
        // str x23, [sp] -> 0xf90003f7
        let code = [0xf7, 0x03, 0x00, 0xf9];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert!(
            instructions[0].touches_x23(),
            "str x23, [sp] should be detected as x23 usage"
        );
    }

    #[test]
    fn test_x23_as_source_operand() {
        // add x0, x1, x23 -> uses x23 as source operand
        // add x0, x1, x23 -> 0x8b170020
        let code = [0x20, 0x00, 0x17, 0x8b];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert!(
            instructions[0].touches_x23(),
            "add x0, x1, x23 should be detected as x23 usage"
        );
    }

    #[test]
    fn test_detect_w23_modification() {
        // mov w23, #1 -> 0x52800037 (MOVZ w23, #1)
        // Malicious: writing to w23 clears x23's upper 32 bits, bypassing gas check
        let code = [0x37, 0x00, 0x80, 0x52];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert!(
            instructions[0].touches_x23(),
            "w23 modification should be detected (clears x23 upper bits)"
        );
        assert!(
            !instructions[0].is_gas_decrement(),
            "mov w23 should not be a valid gas decrement"
        );
    }

    #[test]
    fn test_detect_w23_add() {
        // add w23, w23, #1 -> 0x110006f7
        // Malicious: 32-bit add on gas register alias
        let code = [0xf7, 0x06, 0x00, 0x11];
        let instructions = crate::decode_instructions(&code).unwrap();

        assert_eq!(instructions.len(), 1);
        assert!(
            instructions[0].touches_x23(),
            "w23 usage in add should be detected"
        );
        assert!(
            !instructions[0].is_gas_decrement(),
            "add w23, w23, #1 should not be a valid gas decrement"
        );
    }

    #[test]
    fn test_sp_decrement_sub_sp() {
        // sub sp, sp, #32 -> 0xd10083ff
        let code = [0xff, 0x83, 0x00, 0xd1];
        let instructions = crate::decode_instructions(&code).unwrap();
        assert_eq!(instructions[0].sp_decrement().unwrap(), 32);
    }

    #[test]
    fn test_sp_decrement_stp_preindex() {
        // stp x29, x30, [sp, #-16]! -> 0xa9bf7bfd
        let code = [0xfd, 0x7b, 0xbf, 0xa9];
        let instructions = crate::decode_instructions(&code).unwrap();
        assert_eq!(instructions[0].sp_decrement().unwrap(), 16);
    }

    #[test]
    fn test_sp_decrement_str_preindex() {
        // str x0, [sp, #-16]! -> 0xf81f0fe0
        let code = [0xe0, 0x0f, 0x1f, 0xf8];
        let instructions = crate::decode_instructions(&code).unwrap();
        assert_eq!(instructions[0].sp_decrement().unwrap(), 16);
    }

    #[test]
    fn test_sp_decrement_non_sp_instruction() {
        // add x0, x1, x2 -> 0x8b020020
        let code = [0x20, 0x00, 0x02, 0x8b];
        let instructions = crate::decode_instructions(&code).unwrap();
        assert_eq!(instructions[0].sp_decrement().unwrap(), 0);
    }

    #[test]
    fn test_sp_decrement_sub_register() {
        // sub sp, sp, x0, uxtx — extended register form where Rn=SP, Rd=SP
        // Encoding: 0xcb2063ff  (little-endian: [0xff, 0x63, 0x20, 0xcb])
        let code = [0xff, 0x63, 0x20, 0xcb];
        let instructions = crate::decode_instructions(&code).unwrap();
        assert!(
            instructions[0].sp_decrement().is_err(),
            "sub sp, sp, x0 should return Err (unknown stack decrement)"
        );
    }

    #[test]
    fn test_sp_increment_not_flagged() {
        // add sp, sp, #32 -> 0x910083ff
        let code = [0xff, 0x83, 0x00, 0x91];
        let instructions = crate::decode_instructions(&code).unwrap();
        assert_eq!(instructions[0].sp_decrement().unwrap(), 0);
        assert!(
            !instructions[0].is_unsafe_sp_modification(),
            "add sp, sp, #N is a recognized safe pattern"
        );
    }

    #[test]
    fn test_is_bl() {
        // bl #8 -> 0x94000002
        let code = [0x02, 0x00, 0x00, 0x94];
        let instructions = crate::decode_instructions(&code).unwrap();
        assert!(instructions[0].is_bl());
    }

    #[test]
    fn test_modifies_sp_sub_imm() {
        // sub sp, sp, #32 -> 0xd10083ff
        let code = [0xff, 0x83, 0x00, 0xd1];
        let instructions = crate::decode_instructions(&code).unwrap();
        assert!(instructions[0].modifies_sp());
    }

    #[test]
    fn test_modifies_sp_writeback() {
        // stp x29, x30, [sp, #-16]! -> 0xa9bf7bfd
        let code = [0xfd, 0x7b, 0xbf, 0xa9];
        let instructions = crate::decode_instructions(&code).unwrap();
        assert!(instructions[0].modifies_sp());
    }

    #[test]
    fn test_does_not_modify_sp_read_only() {
        // ldr x0, [sp, #16] (no writeback) -> 0xf94013e0
        let code = [0xe0, 0x13, 0x40, 0xf9];
        let instructions = crate::decode_instructions(&code).unwrap();
        assert!(
            !instructions[0].modifies_sp(),
            "ldr x0, [sp, #16] with no writeback should not modify SP"
        );
    }

    #[test]
    fn test_does_not_modify_sp_cmp() {
        // cmp sp, #0 -> 0xf100001f
        // Although operands[0] is RegisterOrSP(X, 31), CMP doesn't write to it
        let code = [0x1f, 0x00, 0x00, 0xf1];
        let instructions = crate::decode_instructions(&code).unwrap();
        assert!(
            !instructions[0].modifies_sp(),
            "cmp sp, #0 should not modify SP"
        );
    }

    #[test]
    fn test_unsafe_sp_sub_register() {
        // sub sp, sp, x0, uxtx — extended register form where Rn=SP, Rd=SP
        // Encoding: 0xcb2063ff  (little-endian: [0xff, 0x63, 0x20, 0xcb])
        let code = [0xff, 0x63, 0x20, 0xcb];
        let instructions = crate::decode_instructions(&code).unwrap();
        assert!(
            instructions[0].is_unsafe_sp_modification(),
            "sub sp, sp, x0 (register operand) should be unsafe"
        );
    }

    #[test]
    fn test_unsafe_sp_mov() {
        // mov sp, x0 -> 0x9100001f (add sp, x0, #0)
        let code = [0x1f, 0x00, 0x00, 0x91];
        let instructions = crate::decode_instructions(&code).unwrap();
        // This is ADD sp, x0, #0 which writes SP from x0 - not recognized safe pattern
        // (recognized pattern requires both dst AND src to be SP)
        assert!(
            instructions[0].is_unsafe_sp_modification(),
            "mov sp, x0 should be unsafe"
        );
    }

    #[test]
    fn test_unsafe_sp_post_index_reg() {
        // ldr x0, [sp], x1 — post-index with register offset modifies SP
        // This is the LDRAA/LDRAB or similar form; using a simpler approach:
        // Actually, ldr x0, [sp], x1 isn't a standard ARM64 encoding.
        // Use ldp with post-index instead: ldp x0, x1, [sp], #32 is safe (recognized).
        // For a truly unsafe post-index-reg, we need RegPostIndexReg(31, _).
        // This form doesn't exist for standard load/store. Skip this specific test
        // since ARM64 doesn't have a standard post-index-register form for SP loads.
    }

    #[test]
    fn test_safe_sp_patterns_not_flagged() {
        // Pattern 1: sub sp, sp, #32
        let code = [0xff, 0x83, 0x00, 0xd1];
        let instructions = crate::decode_instructions(&code).unwrap();
        assert!(!instructions[0].is_unsafe_sp_modification());

        // Pattern 2: stp x29, x30, [sp, #-16]!
        let code = [0xfd, 0x7b, 0xbf, 0xa9];
        let instructions = crate::decode_instructions(&code).unwrap();
        assert!(!instructions[0].is_unsafe_sp_modification());

        // Pattern 4: add sp, sp, #32
        let code = [0xff, 0x83, 0x00, 0x91];
        let instructions = crate::decode_instructions(&code).unwrap();
        assert!(!instructions[0].is_unsafe_sp_modification());

        // Pattern 5: ldp x29, x30, [sp], #16
        let code = [0xfd, 0x7b, 0xc1, 0xa8];
        let instructions = crate::decode_instructions(&code).unwrap();
        assert!(!instructions[0].is_unsafe_sp_modification());
    }
}
