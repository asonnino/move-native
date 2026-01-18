//! Trait abstractions for instruction classification and CFG construction
//!
//! This module provides two levels of abstraction:
//!
//! - [`BasicInstruction`]: Minimal interface for mnemonic-based classification.
//!   Implemented by both resolved and unresolved instructions.
//!
//! - [`CfgInstruction`]: Full interface for CFG construction, extending
//!   `BasicInstruction` with target information. Implemented by:
//!   - Text assembly: `ResolvedInstruction` (in gas-instrument)
//!   - Binary: `DecodedInstruction` (in native-verifier)

use crate::arm64::ClassifiedOpcode;

/// Minimal interface: instruction with a classifiable mnemonic.
///
/// Provides default implementations for control flow classification
/// using the centralized opcode table. This trait can be implemented
/// by both resolved and unresolved instructions since it only requires
/// a mnemonic.
///
/// # Default Implementations
///
/// All classification methods (`is_branch`, `is_call`, etc.) have default
/// implementations that use [`ClassifiedOpcode::from_mnemonic`] to look up
/// the mnemonic in the opcode table. This ensures consistent classification
/// across text and binary.
pub trait BasicInstruction {
    /// Returns the mnemonic of this instruction.
    fn mnemonic(&self) -> &str;

    /// Check if this is a branch instruction.
    #[inline]
    fn is_branch(&self) -> bool {
        ClassifiedOpcode::from_mnemonic(self.mnemonic()).is_some_and(|c| c.is_branch)
    }

    /// Check if this is an indirect (register-target) branch.
    #[inline]
    fn is_indirect(&self) -> bool {
        ClassifiedOpcode::from_mnemonic(self.mnemonic()).is_some_and(|c| c.is_indirect)
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
}

/// Full interface for CFG construction.
///
/// Extends [`BasicInstruction`] with target information needed for CFG building.
/// Both use `usize` for targets:
/// - Text assembly: instruction index (after label resolution)
/// - Binary: byte offset
///
/// # Requirements
///
/// Every item in the instruction stream must be an actual instruction with a mnemonic.
/// Label-only lines and directives should be filtered out during parsing/resolution.
pub trait CfgInstruction: BasicInstruction {
    /// Returns the branch target if this is a direct branch.
    /// - Text: instruction index
    /// - Binary: byte offset
    fn branch_target(&self) -> Option<usize>;

    /// Returns this instruction's identity as a potential branch target.
    /// - Text: instruction index
    /// - Binary: byte offset
    fn as_target(&self) -> usize;

    /// Check if this is an unconditional jump (not a call or return).
    #[inline]
    fn is_unconditional_jump(&self) -> bool {
        self.is_branch() && !self.is_conditional() && !self.is_call()
    }
}

/// Alias for backwards compatibility.
pub use CfgInstruction as InstructionInfo;
