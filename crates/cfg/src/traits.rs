// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Trait abstractions for instruction classification and CFG construction
//!
//! This module provides two levels of abstraction:
//!
//! - [`BasicInstruction`]: Minimal interface for mnemonic-based classification.
//!   Implemented by both resolved and unresolved instructions.
//!
//! - [`CfgInstruction`]: Full interface for CFG construction, extending
//!   `BasicInstruction` with target information. Implemented by:
//!   - Text assembly: `ResolvedInstruction` (in instrumenter)
//!   - Binary: `DecodedInstruction` (in verifier)

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
        ClassifiedOpcode::from_mnemonic(self.mnemonic()).is_branch
    }

    /// Check if this is an indirect (register-target) branch.
    #[inline]
    fn is_indirect(&self) -> bool {
        ClassifiedOpcode::from_mnemonic(self.mnemonic()).is_indirect
    }

    /// Check if this is a call instruction (BL, BLR, etc.).
    #[inline]
    fn is_call(&self) -> bool {
        ClassifiedOpcode::from_mnemonic(self.mnemonic()).is_call
    }

    /// Check if this is a return instruction (RET, RETAA, etc.).
    #[inline]
    fn is_return(&self) -> bool {
        ClassifiedOpcode::from_mnemonic(self.mnemonic()).is_return
    }

    /// Check if this is a conditional branch.
    #[inline]
    fn is_conditional(&self) -> bool {
        ClassifiedOpcode::from_mnemonic(self.mnemonic()).is_conditional
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
}

#[cfg(test)]
pub(crate) mod mock_instruction {
    use super::{BasicInstruction, CfgInstruction};

    /// Mock instruction for testing trait implementations and CFG construction.
    #[derive(Debug, Clone)]
    pub struct MockInstruction {
        pub mnemonic: &'static str,
        pub index: usize,
        pub target: Option<usize>,
    }

    impl MockInstruction {
        pub fn new(mnemonic: &'static str, index: usize) -> Self {
            Self {
                mnemonic,
                index,
                target: None,
            }
        }

        pub fn with_target(mnemonic: &'static str, index: usize, target: usize) -> Self {
            Self {
                mnemonic,
                index,
                target: Some(target),
            }
        }
    }

    impl BasicInstruction for MockInstruction {
        fn mnemonic(&self) -> &str {
            self.mnemonic
        }
    }

    impl CfgInstruction for MockInstruction {
        fn branch_target(&self) -> Option<usize> {
            self.target
        }

        fn as_target(&self) -> usize {
            self.index
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{mock_instruction::MockInstruction, *};

    #[test]
    fn test_is_branch() {
        // Unconditional branch
        assert!(MockInstruction::new("b", 0).is_branch());

        // Conditional branches
        assert!(MockInstruction::new("b.lt", 0).is_branch());
        assert!(MockInstruction::new("b.eq", 0).is_branch());
        assert!(MockInstruction::new("b.ne", 0).is_branch());

        // Compare and branch
        assert!(MockInstruction::new("cbz", 0).is_branch());
        assert!(MockInstruction::new("cbnz", 0).is_branch());

        // Test and branch
        assert!(MockInstruction::new("tbz", 0).is_branch());
        assert!(MockInstruction::new("tbnz", 0).is_branch());

        // Call is a branch
        assert!(MockInstruction::new("bl", 0).is_branch());

        // Return is a branch
        assert!(MockInstruction::new("ret", 0).is_branch());
    }

    #[test]
    fn test_is_conditional() {
        // Conditional branches
        assert!(MockInstruction::new("b.lt", 0).is_conditional());
        assert!(MockInstruction::new("b.eq", 0).is_conditional());
        assert!(MockInstruction::new("b.ne", 0).is_conditional());
        assert!(MockInstruction::new("b.ge", 0).is_conditional());

        // Compare and branch are conditional
        assert!(MockInstruction::new("cbz", 0).is_conditional());
        assert!(MockInstruction::new("cbnz", 0).is_conditional());

        // Test and branch are conditional
        assert!(MockInstruction::new("tbz", 0).is_conditional());
        assert!(MockInstruction::new("tbnz", 0).is_conditional());

        // Unconditional branch is not conditional
        assert!(!MockInstruction::new("b", 0).is_conditional());

        // Call is not conditional
        assert!(!MockInstruction::new("bl", 0).is_conditional());

        // Return is not conditional
        assert!(!MockInstruction::new("ret", 0).is_conditional());
    }

    #[test]
    fn test_is_call() {
        // BL is a call
        assert!(MockInstruction::new("bl", 0).is_call());

        // BLR is a call (indirect)
        assert!(MockInstruction::new("blr", 0).is_call());

        // B is not a call
        assert!(!MockInstruction::new("b", 0).is_call());

        // Conditional branches are not calls
        assert!(!MockInstruction::new("b.lt", 0).is_call());

        // Return is not a call
        assert!(!MockInstruction::new("ret", 0).is_call());
    }

    #[test]
    fn test_is_return() {
        // RET is a return
        assert!(MockInstruction::new("ret", 0).is_return());

        // RETAA/RETAB are returns
        assert!(MockInstruction::new("retaa", 0).is_return());
        assert!(MockInstruction::new("retab", 0).is_return());

        // B is not a return
        assert!(!MockInstruction::new("b", 0).is_return());

        // BL is not a return
        assert!(!MockInstruction::new("bl", 0).is_return());
    }

    #[test]
    fn test_non_branch_classification() {
        // Arithmetic instructions are not branches
        assert!(!MockInstruction::new("mov", 0).is_branch());
        assert!(!MockInstruction::new("add", 0).is_branch());
        assert!(!MockInstruction::new("sub", 0).is_branch());
        assert!(!MockInstruction::new("mul", 0).is_branch());
        assert!(!MockInstruction::new("ldr", 0).is_branch());
        assert!(!MockInstruction::new("str", 0).is_branch());
        assert!(!MockInstruction::new("cmp", 0).is_branch());

        // They're also not conditional, call, or return
        assert!(!MockInstruction::new("add", 0).is_conditional());
        assert!(!MockInstruction::new("add", 0).is_call());
        assert!(!MockInstruction::new("add", 0).is_return());
    }

    #[test]
    fn test_is_indirect() {
        // Register branches are indirect
        assert!(MockInstruction::new("br", 0).is_indirect());
        assert!(MockInstruction::new("blr", 0).is_indirect());
        assert!(MockInstruction::new("ret", 0).is_indirect());

        // Label branches are not indirect
        assert!(!MockInstruction::new("b", 0).is_indirect());
        assert!(!MockInstruction::new("bl", 0).is_indirect());
        assert!(!MockInstruction::new("b.lt", 0).is_indirect());
    }

    #[test]
    fn test_classification_invariants() {
        // All returns are branches
        for mnemonic in ["ret", "retaa", "retab"] {
            let instruction = MockInstruction::new(mnemonic, 0);
            assert!(instruction.is_return());
            assert!(instruction.is_branch());
        }

        // All calls are branches
        for mnemonic in ["bl", "blr"] {
            let instruction = MockInstruction::new(mnemonic, 0);
            assert!(instruction.is_call());
            assert!(instruction.is_branch());
        }

        // All indirect branches are branches
        for mnemonic in ["br", "blr", "ret"] {
            let instruction = MockInstruction::new(mnemonic, 0);
            assert!(instruction.is_indirect());
            assert!(instruction.is_branch());
        }

        // All conditional instructions are branches
        for mnemonic in ["b.lt", "b.eq", "b.ne", "cbz", "cbnz", "tbz", "tbnz"] {
            let instruction = MockInstruction::new(mnemonic, 0);
            assert!(instruction.is_conditional());
            assert!(instruction.is_branch());
        }
    }
}
