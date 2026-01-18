//! Trait abstractions for CFG construction
//!
//! The [`InstructionInfo`] trait provides a unified interface for instruction
//! properties needed by the CFG builder. It is implemented by:
//! - Text assembly: `ResolvedInstruction` (in gas-instrument)
//! - Binary: `DecodedInstruction` (in native-verifier)

use crate::arm64::ClassifiedOpcode;

/// Information about an instruction needed for CFG construction.
///
/// This trait abstracts over the differences between text assembly and binary.
/// Both use `usize` for targets, but with different semantics:
/// - Text assembly: instruction index (after label resolution)
/// - Binary: byte offset
///
/// # Requirements
///
/// Every item in the instruction stream must be an actual instruction with a mnemonic.
/// Label-only lines and directives should be filtered out during parsing/resolution.
///
/// # Default Implementations
///
/// Control flow methods (`is_branch`, `is_call`, etc.) have default implementations
/// that use [`ClassifiedOpcode::from_mnemonic`] to look up the mnemonic in the
/// opcode table. This ensures consistent classification across text and binary.
pub trait InstructionInfo {
    /// Returns the mnemonic of this instruction.
    fn mnemonic(&self) -> &str;

    /// Returns the branch target if this is a direct branch.
    /// - Text: instruction index
    /// - Binary: byte offset
    fn branch_target(&self) -> Option<usize>;

    /// Returns this instruction's identity as a potential branch target.
    /// - Text: instruction index
    /// - Binary: byte offset
    fn as_target(&self) -> usize;

    /// Check if this is a branch instruction.
    #[inline]
    fn is_branch(&self) -> bool {
        ClassifiedOpcode::from_mnemonic(self.mnemonic()).is_some_and(|c| c.is_branch)
    }

    /// Check if this is a call instruction (BL, BLR, etc.).
    #[inline]
    fn is_call(&self) -> bool {
        ClassifiedOpcode::from_mnemonic(self.mnemonic()).is_some_and(|c| c.is_call)
    }

    /// Check if this is a return instruction (RET, RETAA, etc.).
    #[inline]
    fn is_return(&self) -> bool {
        ClassifiedOpcode::from_mnemonic(self.mnemonic()).is_some_and(|c| c.is_return)
    }

    /// Check if this is a conditional branch.
    #[inline]
    fn is_conditional(&self) -> bool {
        ClassifiedOpcode::from_mnemonic(self.mnemonic()).is_some_and(|c| c.is_conditional)
    }

    /// Check if this is an unconditional jump (not a call or return).
    #[inline]
    fn is_unconditional_jump(&self) -> bool {
        self.is_branch() && !self.is_conditional() && !self.is_call()
    }
}
