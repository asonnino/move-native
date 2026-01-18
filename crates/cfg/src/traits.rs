//! Trait abstractions for CFG construction
//!
//! The [`InstructionInfo`] trait provides a unified interface for instruction
//! properties needed by the CFG builder. It is implemented by:
//! - Text assembly: `IndexedParsedLine` (in gas-instrument)
//! - Binary: `DecodedInstruction` (in native-verifier)

use std::hash::Hash;

use crate::arm64::ClassifiedOpcode;

/// Information about an instruction needed for CFG construction.
///
/// This trait abstracts over the differences between text assembly and binary:
/// - Text assembly uses line indices for positions and label strings for targets
/// - Binary uses byte offsets for both positions and targets
///
/// # Associated Types
///
/// - `Position`: Where the instruction is in the sequence (line index or byte offset)
/// - `Target`: How branch targets are represented (label string or byte offset)
///
/// # Default Implementations
///
/// Control flow methods (`is_branch`, `is_call`, etc.) have default implementations
/// that use [`ClassifiedOpcode::from_mnemonic`] to look up the mnemonic in the
/// opcode table. This ensures consistent classification across text and binary.
pub trait InstructionInfo {
    /// Position in instruction stream.
    /// - Text: line index (`usize`)
    /// - Binary: byte offset (`usize`)
    type Position: Copy + Ord + Hash;

    /// Branch target type.
    /// - Text: label name (`String`)
    /// - Binary: byte offset (`usize`)
    type Target: Eq + Hash + Clone;

    /// Returns the position of this instruction.
    fn position(&self) -> Self::Position;

    /// Returns the mnemonic of this instruction, or `None` if this is a label-only line.
    fn mnemonic(&self) -> Option<&str>;

    /// Returns the branch target if this is a direct branch.
    fn branch_target(&self) -> Option<Self::Target>;

    /// Returns the label at this position (for text assembly), or `None`.
    fn label(&self) -> Option<Self::Target>;

    /// Converts position to target type for comparison.
    ///
    /// - Text: returns `None` (labels determine block boundaries, not position comparison)
    /// - Binary: returns `Some(offset)` to check if this position is a branch target
    fn position_as_target(&self) -> Option<Self::Target>;

    /// Check if this is a branch instruction.
    #[inline]
    fn is_branch(&self) -> bool {
        self.mnemonic()
            .and_then(ClassifiedOpcode::from_mnemonic)
            .is_some_and(|c| c.is_branch)
    }

    /// Check if this is a call instruction (BL, BLR, etc.).
    #[inline]
    fn is_call(&self) -> bool {
        self.mnemonic()
            .and_then(ClassifiedOpcode::from_mnemonic)
            .is_some_and(|c| c.is_call)
    }

    /// Check if this is a return instruction (RET, RETAA, etc.).
    #[inline]
    fn is_return(&self) -> bool {
        self.mnemonic()
            .and_then(ClassifiedOpcode::from_mnemonic)
            .is_some_and(|c| c.is_return)
    }

    /// Check if this is a conditional branch.
    #[inline]
    fn is_conditional(&self) -> bool {
        self.mnemonic()
            .and_then(ClassifiedOpcode::from_mnemonic)
            .is_some_and(|c| c.is_conditional)
    }

    /// Check if this is an unconditional jump (not a call or return).
    #[inline]
    fn is_unconditional_jump(&self) -> bool {
        self.is_branch() && !self.is_conditional() && !self.is_call()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Mock instruction for testing
    struct MockInstruction {
        position: usize,
        mnemonic: Option<&'static str>,
        target: Option<String>,
        label: Option<String>,
    }

    impl InstructionInfo for MockInstruction {
        type Position = usize;
        type Target = String;

        fn position(&self) -> usize {
            self.position
        }

        fn mnemonic(&self) -> Option<&str> {
            self.mnemonic
        }

        fn branch_target(&self) -> Option<String> {
            self.target.clone()
        }

        fn label(&self) -> Option<String> {
            self.label.clone()
        }

        fn position_as_target(&self) -> Option<String> {
            None // Text-like behavior
        }
    }

    #[test]
    fn test_is_branch_unconditional() {
        let inst = MockInstruction {
            position: 0,
            mnemonic: Some("b"),
            target: Some(".Lloop".to_string()),
            label: None,
        };
        assert!(inst.is_branch());
        assert!(!inst.is_conditional());
        assert!(!inst.is_call());
        assert!(inst.is_unconditional_jump());
    }

    #[test]
    fn test_is_branch_conditional() {
        let inst = MockInstruction {
            position: 0,
            mnemonic: Some("b.eq"),
            target: Some(".Lthen".to_string()),
            label: None,
        };
        assert!(inst.is_branch());
        assert!(inst.is_conditional());
        assert!(!inst.is_unconditional_jump());
    }

    #[test]
    fn test_is_call() {
        let inst = MockInstruction {
            position: 0,
            mnemonic: Some("bl"),
            target: Some("_helper".to_string()),
            label: None,
        };
        assert!(inst.is_branch());
        assert!(inst.is_call());
        assert!(!inst.is_unconditional_jump()); // calls are not "jumps"
    }

    #[test]
    fn test_is_return() {
        let inst = MockInstruction {
            position: 0,
            mnemonic: Some("ret"),
            target: None,
            label: None,
        };
        assert!(inst.is_branch());
        assert!(inst.is_return());
    }

    #[test]
    fn test_non_branch() {
        let inst = MockInstruction {
            position: 0,
            mnemonic: Some("add"),
            target: None,
            label: None,
        };
        assert!(!inst.is_branch());
        assert!(!inst.is_call());
        assert!(!inst.is_return());
        assert!(!inst.is_conditional());
        assert!(!inst.is_unconditional_jump());
    }

    #[test]
    fn test_label_only_line() {
        let inst = MockInstruction {
            position: 0,
            mnemonic: None,
            target: None,
            label: Some(".Lloop".to_string()),
        };
        assert!(!inst.is_branch());
        assert!(inst.label().is_some());
    }

    #[test]
    fn test_unknown_mnemonic() {
        let inst = MockInstruction {
            position: 0,
            mnemonic: Some("notarealinstruction"),
            target: None,
            label: None,
        };
        // Unknown mnemonics are not branches
        assert!(!inst.is_branch());
        assert!(!inst.is_call());
    }
}
