// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Arm64 assembly text parser.
//!
//! Parses GNU-style assembly syntax as produced by LLVM/GCC.
//!
//! # Two-Phase Parsing
//!
//! Parsing happens in two phases:
//!
//! 1. **Text parsing** ([`ParsedAssembly::parse`]): Splits input into lines,
//!    identifies labels, directives, and instructions. No validation is done.
//!
//! 2. **Label resolution** ([`ParsedAssembly::resolve`]): Filters to actual
//!    instructions and resolves branch target labels to instruction indices.

use std::collections::HashMap;

use cfg::{BasicInstruction, CfgInstruction};

use crate::error::ResolveError;

/// A resolved instruction with branch targets as instruction indices.
///
/// This is the output of [`ParsedAssembly::resolve`]. Each instance represents
/// an actual CPU instruction (no label-only lines or directives).
#[derive(Debug, Clone)]
pub(crate) struct ResolvedInstruction {
    /// Index in the resolved instruction stream (0-based).
    pub(crate) index: usize,
    /// The instruction mnemonic (e.g., "mov", "b.lt", "ret").
    pub(crate) mnemonic: String,
    /// Branch target as instruction index, if this is a direct branch.
    pub(crate) branch_target: Option<usize>,
    /// Original source line number (1-indexed).
    pub(crate) line_number: usize,
}

impl BasicInstruction for ResolvedInstruction {
    fn mnemonic(&self) -> &str {
        &self.mnemonic
    }
}

impl CfgInstruction for ResolvedInstruction {
    fn branch_target(&self) -> Option<usize> {
        self.branch_target
    }

    fn as_target(&self) -> usize {
        self.index
    }
}

/// The content of an assembly line after any label.
pub(crate) enum Statement<'a> {
    /// A CPU instruction.
    Instruction(UnresolvedInstruction<'a>),
    /// An assembler directive (e.g., `.global`, `.align`).
    Directive,
    /// Empty line or label-only.
    Empty,
}

/// An unresolved instruction with operands as raw strings.
///
/// Branch targets are still label names, not instruction indices.
pub(crate) struct UnresolvedInstruction<'a> {
    /// The mnemonic (e.g., "mov", "b.lt", "ret").
    pub(crate) mnemonic: &'a str,
    /// Operands as raw strings (e.g., `["x0", "#0"]` or `["x0", "[sp, #16]"]`).
    pub(crate) operands: Vec<&'a str>,
}

impl<'a> UnresolvedInstruction<'a> {
    /// Parse an instruction from text (after removing label and comments).
    fn parse(text: &'a str) -> Self {
        let text = text.trim();

        // Split into mnemonic and operands
        let mut parts = text.splitn(2, |c: char| c.is_whitespace());
        let mnemonic = parts.next().unwrap_or("");
        let operands_str = parts.next().unwrap_or("");

        let operands = Self::parse_operands(operands_str);

        Self { mnemonic, operands }
    }

    /// Parse comma-separated operands, respecting brackets for addressing modes.
    ///
    /// Commas inside `[...]` are not treated as separators.
    fn parse_operands(s: &'a str) -> Vec<&'a str> {
        let s = s.trim();
        if s.is_empty() {
            return Vec::new();
        }

        let mut operands = Vec::new();
        let mut start = 0;
        let mut bracket_depth: usize = 0;

        for (i, c) in s.char_indices() {
            match c {
                '[' => bracket_depth += 1,
                ']' => bracket_depth = bracket_depth.saturating_sub(1),
                ',' if bracket_depth == 0 => {
                    let operand = s[start..i].trim();
                    if !operand.is_empty() {
                        operands.push(operand);
                    }
                    start = i + 1;
                }
                _ => {}
            }
        }

        // Last operand
        let operand = s[start..].trim();
        if !operand.is_empty() {
            operands.push(operand);
        }

        operands
    }

    /// Get the branch target label, if this is a direct branch.
    ///
    /// Returns `None` for:
    /// - Non-branch instructions
    /// - Indirect branches (br, blr, ret) where the target is a register
    fn branch_target_label(&self) -> Option<&str> {
        if !self.is_branch() || self.is_indirect() {
            return None;
        }
        self.operands.last().copied()
    }
}

impl BasicInstruction for UnresolvedInstruction<'_> {
    fn mnemonic(&self) -> &str {
        self.mnemonic
    }
}

/// A parsed line from an assembly file.
pub struct ParsedLine<'a> {
    /// Label defined on this line (e.g., `".Lloop"` from `".Lloop:"`).
    pub(crate) label: Option<&'a str>,
    /// The statement on this line.
    pub(crate) statement: Statement<'a>,
    /// Original line number (1-indexed).
    pub(crate) line_number: usize,
    /// Original line text (for reconstruction or error messages).
    pub(crate) original: &'a str,
}

/// Parsed assembly text, ready for resolution or inspection.
/// let instructions = asm.resolve()?;
pub struct ParsedAssembly<'a> {
    lines: Vec<ParsedLine<'a>>,
}

impl<'a> ParsedAssembly<'a> {
    /// Parse assembly text into lines.
    ///
    /// This performs text parsing only. No validation is done on mnemonics
    /// or operands. Labels are not yet resolved to instruction indices.
    pub fn parse(input: &'a str) -> Self {
        let lines = input
            .lines()
            .enumerate()
            .map(|(idx, text)| Self::parse_line(text, idx + 1))
            .collect();
        Self { lines }
    }

    /// Resolve labels to instruction indices.
    ///
    /// This filters to only actual instructions (skipping label-only lines,
    /// directives, and empty lines) and resolves branch target labels to
    /// instruction indices.
    ///
    /// # Errors
    ///
    /// - [`ResolveError::TrailingLabels`]: Labels at end of file with no instruction
    /// - [`ResolveError::UndefinedLabel`]: Branch references an undefined label
    pub(crate) fn resolve(&self) -> Result<Vec<ResolvedInstruction>, ResolveError> {
        // First pass: build instructions, collect labels
        let mut instructions: Vec<ResolvedInstruction> = Vec::new();
        let mut branch_labels: Vec<Option<&str>> = Vec::new();
        let mut pending_labels: Vec<&str> = Vec::new();
        let mut label_to_index: HashMap<&str, usize> = HashMap::new();

        for line in &self.lines {
            if let Some(label) = line.label {
                pending_labels.push(label);
            }

            if let Statement::Instruction(ref instruction) = line.statement {
                let index = instructions.len();

                // All pending labels point to this instruction
                for label in pending_labels.drain(..) {
                    label_to_index.insert(label, index);
                }

                instructions.push(ResolvedInstruction {
                    index,
                    mnemonic: instruction.mnemonic.to_string(),
                    branch_target: None, // to be resolved in second pass
                    line_number: line.line_number,
                });
                branch_labels.push(instruction.branch_target_label());
            }
        }

        if !pending_labels.is_empty() {
            return Err(ResolveError::TrailingLabels(
                pending_labels.into_iter().map(String::from).collect(),
            ));
        }

        // Second pass: resolve branch targets
        for (instruction, label) in instructions.iter_mut().zip(branch_labels.iter()) {
            if let Some(label) = label {
                let target = label_to_index.get(label).copied().ok_or_else(|| {
                    ResolveError::UndefinedLabel {
                        label: label.to_string(),
                        line: instruction.line_number,
                    }
                })?;
                instruction.branch_target = Some(target);
            }
        }

        Ok(instructions)
    }

    /// Access the parsed lines for inspection.
    pub fn lines(&self) -> &[ParsedLine<'a>] {
        &self.lines
    }

    /// Parse a single line of assembly.
    fn parse_line(text: &'a str, line_number: usize) -> ParsedLine<'a> {
        let original = text;
        let text = Self::strip_comment(text).trim();

        if text.is_empty() {
            return ParsedLine {
                label: None,
                statement: Statement::Empty,
                line_number,
                original,
            };
        }

        let (label, rest) = Self::split_label(text);

        // Empty line after label
        if rest.is_empty() {
            return ParsedLine {
                label,
                statement: Statement::Empty,
                line_number,
                original,
            };
        }

        // Directive
        if rest.starts_with('.') {
            return ParsedLine {
                label,
                statement: Statement::Directive,
                line_number,
                original,
            };
        }

        // Must be an instruction
        ParsedLine {
            label,
            statement: Statement::Instruction(UnresolvedInstruction::parse(rest)),
            line_number,
            original,
        }
    }

    /// Remove comments from a line.
    ///
    /// Supports: `//`, `/*`, `;`, `@`
    ///
    /// TODO: Multi-line `/* ... */` comments are not handled (strips from `/*` to EOL only).
    /// TODO: `#` comments (used by some assemblers) are not supported.
    fn strip_comment(line: &str) -> &str {
        let mut end = line.len();

        if let Some(pos) = line.find("//") {
            end = end.min(pos);
        }
        if let Some(pos) = line.find("/*") {
            end = end.min(pos);
        }
        if let Some(pos) = line.find(';') {
            end = end.min(pos);
        }
        if let Some(pos) = line.find('@') {
            end = end.min(pos);
        }

        &line[..end]
    }

    /// Split a line into optional label and remaining text.
    fn split_label(line: &str) -> (Option<&str>, &str) {
        if let Some(colon_pos) = Self::find_label_colon(line) {
            let label = line[..colon_pos].trim();
            let rest = line[colon_pos + 1..].trim();
            (Some(label), rest)
        } else {
            (None, line)
        }
    }

    /// Find position of label-ending colon.
    ///
    /// Valid label characters: alphanumeric, `_`, `.`, `$`
    fn find_label_colon(line: &str) -> Option<usize> {
        let mut chars = line.char_indices().peekable();

        // Skip leading whitespace
        while let Some(&(_, c)) = chars.peek() {
            if !c.is_whitespace() {
                break;
            }
            chars.next();
        }

        // Scan label characters
        for (pos, c) in chars {
            if c == ':' {
                return Some(pos);
            }
            if c.is_alphanumeric() || c == '_' || c == '.' || c == '$' {
                continue;
            }
            break;
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use cfg::{BasicInstruction, CfgInstruction};
    use indoc::indoc;

    use super::{ParsedAssembly, ParsedLine, ResolveError, Statement, UnresolvedInstruction};

    fn parse_single_line(text: &str) -> ParsedLine<'_> {
        ParsedAssembly::parse_line(text, 1)
    }

    fn get_instruction<'a>(line: &'a ParsedLine<'a>) -> &'a UnresolvedInstruction<'a> {
        match &line.statement {
            Statement::Instruction(instruction) => instruction,
            _ => panic!("expected instruction"),
        }
    }

    // Basic line parsing

    #[test]
    fn test_empty_line() {
        let line = parse_single_line("");
        assert!(line.label.is_none());
        assert!(matches!(line.statement, Statement::Empty));
    }

    #[test]
    fn test_whitespace_only() {
        let line = parse_single_line("    \t  ");
        assert!(line.label.is_none());
        assert!(matches!(line.statement, Statement::Empty));
    }

    #[test]
    fn test_label_only() {
        let line = parse_single_line(".Lloop:");
        assert_eq!(line.label, Some(".Lloop"));
        assert!(matches!(line.statement, Statement::Empty));
    }

    #[test]
    fn test_label_with_instruction() {
        let line = parse_single_line("_start: mov x0, #1");
        assert_eq!(line.label, Some("_start"));
        let instruction = get_instruction(&line);
        assert_eq!(instruction.mnemonic, "mov");
        assert_eq!(instruction.operands, vec!["x0", "#1"]);
    }

    #[test]
    fn test_directive() {
        let line = parse_single_line(".global _start");
        assert!(line.label.is_none());
        assert!(matches!(line.statement, Statement::Directive));
    }

    #[test]
    fn test_label_with_directive() {
        let line = parse_single_line("my_data: .quad 0x1234");
        assert_eq!(line.label, Some("my_data"));
        assert!(matches!(line.statement, Statement::Directive));
    }

    #[test]
    fn test_simple_instruction() {
        let line = parse_single_line("    mov x0, #0");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.mnemonic, "mov");
        assert_eq!(instruction.operands, vec!["x0", "#0"]);
    }

    #[test]
    fn test_instruction_no_operands() {
        let line = parse_single_line("    ret");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.mnemonic, "ret");
        assert!(instruction.operands.is_empty());

        let line = parse_single_line("    nop");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.mnemonic, "nop");
        assert!(instruction.operands.is_empty());
    }

    #[test]
    fn test_three_operand_instruction() {
        let line = parse_single_line("    add x0, x1, x2");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.mnemonic, "add");
        assert_eq!(instruction.operands, vec!["x0", "x1", "x2"]);
    }

    // Memory addressing operands

    #[test]
    fn test_simple_memory_operand() {
        let line = parse_single_line("    ldr x0, [x1, #8]");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.mnemonic, "ldr");
        assert_eq!(instruction.operands, vec!["x0", "[x1, #8]"]);
    }

    #[test]
    fn test_post_index_addressing() {
        let line = parse_single_line("    ldr x0, [x1], #8");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.operands, vec!["x0", "[x1]", "#8"]);
    }

    #[test]
    fn test_pre_index_writeback() {
        let line = parse_single_line("    ldr x0, [x1, #8]!");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.operands, vec!["x0", "[x1, #8]!"]);
    }

    #[test]
    fn test_ldp_stp_pair() {
        let line = parse_single_line("    ldp x0, x1, [sp, #16]");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.mnemonic, "ldp");
        assert_eq!(instruction.operands, vec!["x0", "x1", "[sp, #16]"]);

        let line = parse_single_line("    stp x29, x30, [sp, #-16]!");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.mnemonic, "stp");
        assert_eq!(instruction.operands, vec!["x29", "x30", "[sp, #-16]!"]);
    }

    // Comments

    #[test]
    fn test_semicolon_comment() {
        let line = parse_single_line("    mov x0, #0 ; initialize counter");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.mnemonic, "mov");
        assert_eq!(instruction.operands, vec!["x0", "#0"]);
    }

    #[test]
    fn test_at_sign_comment() {
        let line = parse_single_line("    add x0, x0, #1 @ increment");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.mnemonic, "add");
        assert_eq!(instruction.operands, vec!["x0", "x0", "#1"]);
    }

    #[test]
    fn test_cpp_style_comment() {
        let line = parse_single_line("    ret // return to caller");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.mnemonic, "ret");
    }

    #[test]
    fn test_c_style_comment() {
        let line = parse_single_line("    nop /* do nothing */");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.mnemonic, "nop");
    }

    #[test]
    fn test_comment_only_line() {
        let line = parse_single_line("; this is a comment");
        assert!(matches!(line.statement, Statement::Empty));

        let line = parse_single_line("@ GNU style comment");
        assert!(matches!(line.statement, Statement::Empty));

        let line = parse_single_line("// C++ comment");
        assert!(matches!(line.statement, Statement::Empty));
    }

    #[test]
    fn test_earliest_comment_wins() {
        let line = parse_single_line("    mov x0, #1 ; comment // not parsed");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.operands, vec!["x0", "#1"]);

        let line = parse_single_line("    mov x0, #2 // comment ; not parsed");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.operands, vec!["x0", "#2"]);
    }

    #[test]
    fn test_original_preserves_comments() {
        let line = parse_single_line("    mov x0, #0 ; comment");
        assert_eq!(line.original, "    mov x0, #0 ; comment");
    }

    // Label formats

    #[test]
    fn test_local_label() {
        let line = parse_single_line(".Lloop:");
        assert_eq!(line.label, Some(".Lloop"));
    }

    #[test]
    fn test_global_label() {
        let line = parse_single_line("_my_function:");
        assert_eq!(line.label, Some("_my_function"));
    }

    #[test]
    fn test_label_with_dollar_sign() {
        let line = parse_single_line("$Lfoo$bar:");
        assert_eq!(line.label, Some("$Lfoo$bar"));
    }

    #[test]
    fn test_label_with_numbers() {
        let line = parse_single_line("loop123:");
        assert_eq!(line.label, Some("loop123"));
    }

    // Branch instructions

    #[test]
    fn test_unconditional_branch() {
        let line = parse_single_line("    b .Lloop");
        let instruction = get_instruction(&line);
        assert!(instruction.is_branch());
        assert!(!instruction.is_conditional());
        assert!(!instruction.is_indirect());
        assert_eq!(instruction.branch_target_label(), Some(".Lloop"));
    }

    #[test]
    fn test_conditional_branch() {
        let line = parse_single_line("    b.lt .Lloop");
        let instruction = get_instruction(&line);
        assert!(instruction.is_branch());
        assert!(instruction.is_conditional());
        assert_eq!(instruction.branch_target_label(), Some(".Lloop"));
    }

    #[test]
    fn test_branch_with_link() {
        let line = parse_single_line("    bl _function");
        let instruction = get_instruction(&line);
        assert!(instruction.is_branch());
        assert!(instruction.is_call());
        assert!(!instruction.is_conditional());
        assert_eq!(instruction.branch_target_label(), Some("_function"));
    }

    #[test]
    fn test_cbz_cbnz() {
        let line = parse_single_line("    cbz x0, .Lzero");
        let instruction = get_instruction(&line);
        assert!(instruction.is_branch());
        assert!(instruction.is_conditional());
        assert_eq!(instruction.branch_target_label(), Some(".Lzero"));

        let line = parse_single_line("    cbnz w5, .Lnonzero");
        let instruction = get_instruction(&line);
        assert!(instruction.is_branch());
        assert!(instruction.is_conditional());
        assert_eq!(instruction.branch_target_label(), Some(".Lnonzero"));
    }

    #[test]
    fn test_tbz_tbnz() {
        let line = parse_single_line("    tbz x0, #63, .Lpositive");
        let instruction = get_instruction(&line);
        assert!(instruction.is_branch());
        assert!(instruction.is_conditional());
        assert_eq!(instruction.operands.len(), 3);
        assert_eq!(instruction.branch_target_label(), Some(".Lpositive"));

        let line = parse_single_line("    tbnz w1, #0, .Lodd");
        let instruction = get_instruction(&line);
        assert!(instruction.is_branch());
        assert_eq!(instruction.branch_target_label(), Some(".Lodd"));
    }

    #[test]
    fn test_indirect_branch_br() {
        let line = parse_single_line("    br x0");
        let instruction = get_instruction(&line);
        assert!(instruction.is_branch());
        assert!(instruction.is_indirect());
        assert!(!instruction.is_conditional());
        assert_eq!(instruction.branch_target_label(), None);
    }

    #[test]
    fn test_indirect_branch_blr() {
        let line = parse_single_line("    blr x30");
        let instruction = get_instruction(&line);
        assert!(instruction.is_branch());
        assert!(instruction.is_indirect());
        assert!(instruction.is_call());
        assert_eq!(instruction.branch_target_label(), None);
    }

    #[test]
    fn test_return() {
        let line = parse_single_line("    ret");
        let instruction = get_instruction(&line);
        assert!(instruction.is_branch());
        assert!(instruction.is_return());
        assert!(instruction.is_indirect());
        assert_eq!(instruction.branch_target_label(), None);
    }

    #[test]
    fn test_all_condition_codes() {
        // Only test condition codes defined in the opcode table
        let conditions = [
            "b.eq", "b.ne", "b.mi", "b.pl", "b.vs", "b.vc", "b.hi", "b.ls", "b.ge", "b.lt", "b.gt",
            "b.le", "b.al",
        ];

        for cond in conditions {
            let input = format!("    {} .Ltarget", cond);
            let line = parse_single_line(&input);
            let instruction = get_instruction(&line);
            assert!(instruction.is_branch(), "{} should be a branch", cond);
            assert!(
                instruction.is_conditional(),
                "{} should be conditional",
                cond
            );
            assert_eq!(instruction.branch_target_label(), Some(".Ltarget"));
        }
    }

    #[test]
    fn test_non_branch_has_no_target() {
        let line = parse_single_line("    add x0, x1, x2");
        let instruction = get_instruction(&line);
        assert!(!instruction.is_branch());
        assert_eq!(instruction.branch_target_label(), None);
    }

    // Multi-line parsing

    #[test]
    fn test_multi_line_parsing() {
        let input = indoc! {"
            .global _start
            _start:
                mov x0, #0
            .Lloop:
                add x0, x0, #1
                cmp x0, #10
                b.lt .Lloop
                ret
        "};
        let asm = ParsedAssembly::parse(input);
        assert_eq!(asm.lines().len(), 8);

        assert_eq!(asm.lines()[0].line_number, 1);
        assert_eq!(asm.lines()[1].line_number, 2);
        assert_eq!(asm.lines()[7].line_number, 8);

        assert!(matches!(asm.lines()[0].statement, Statement::Directive));
        assert_eq!(asm.lines()[1].label, Some("_start"));
        assert_eq!(asm.lines()[3].label, Some(".Lloop"));

        let last_instruction = get_instruction(&asm.lines()[7]);
        assert!(last_instruction.is_return());
    }

    // Label resolution

    #[test]
    fn test_resolve_simple_loop() {
        let input = indoc! {"
            .Lloop:
                add x0, x0, #1
                b.lt .Lloop
        "};
        let asm = ParsedAssembly::parse(input);
        let instructions = asm.resolve().unwrap();

        assert_eq!(instructions.len(), 2);
        assert_eq!(instructions[0].mnemonic, "add");
        assert_eq!(instructions[0].index, 0);
        assert_eq!(instructions[0].branch_target, None);

        assert_eq!(instructions[1].mnemonic, "b.lt");
        assert_eq!(instructions[1].index, 1);
        assert_eq!(instructions[1].branch_target, Some(0));
    }

    #[test]
    fn test_resolve_forward_branch() {
        let input = indoc! {"
                cbz x0, .Lskip
                add x0, x0, #1
            .Lskip:
                ret
        "};
        let asm = ParsedAssembly::parse(input);
        let instructions = asm.resolve().unwrap();

        assert_eq!(instructions.len(), 3);
        assert_eq!(instructions[0].branch_target, Some(2));
        assert_eq!(instructions[2].mnemonic, "ret");
    }

    #[test]
    fn test_resolve_multiple_labels_same_instruction() {
        let input = indoc! {"
            .Lalias1:
            .Lalias2:
                ret
        "};
        let asm = ParsedAssembly::parse(input);
        let instructions = asm.resolve().unwrap();

        assert_eq!(instructions.len(), 1);
        assert_eq!(instructions[0].index, 0);
    }

    #[test]
    fn test_resolve_skips_directives() {
        let input = indoc! {"
            .global _start
            .align 4
            _start:
                mov x0, #0
                ret
        "};
        let asm = ParsedAssembly::parse(input);
        let instructions = asm.resolve().unwrap();

        assert_eq!(instructions.len(), 2);
        assert_eq!(instructions[0].mnemonic, "mov");
        assert_eq!(instructions[1].mnemonic, "ret");
    }

    #[test]
    fn test_resolve_preserves_line_numbers() {
        let input = indoc! {"
            .global _start

            _start:
                mov x0, #0

                ret
        "};
        let asm = ParsedAssembly::parse(input);
        let instructions = asm.resolve().unwrap();

        assert_eq!(instructions[0].line_number, 4);
        assert_eq!(instructions[1].line_number, 6);
    }

    #[test]
    fn test_resolve_error_trailing_labels() {
        let input = indoc! {"
                mov x0, #0
            .Ldangling:
        "};
        let asm = ParsedAssembly::parse(input);
        let result = asm.resolve();

        assert!(matches!(
            result,
            Err(ResolveError::TrailingLabels(ref labels)) if labels == &[".Ldangling"]
        ));
    }

    #[test]
    fn test_resolve_error_undefined_label() {
        let input = indoc! {"
                b .Lmissing
                ret
        "};
        let asm = ParsedAssembly::parse(input);
        let result = asm.resolve();

        assert!(matches!(
            result,
            Err(ResolveError::UndefinedLabel { ref label, line: 1 }) if label == ".Lmissing"
        ));
    }

    #[test]
    fn test_resolve_call_target() {
        let input = indoc! {"
                bl _helper
            _helper:
                ret
        "};
        let asm = ParsedAssembly::parse(input);
        let instructions = asm.resolve().unwrap();

        assert_eq!(instructions[0].branch_target, Some(1));
    }

    #[test]
    fn test_resolve_indirect_branch_no_target() {
        let input = indoc! {"
                blr x0
                ret
        "};
        let asm = ParsedAssembly::parse(input);
        let instructions = asm.resolve().unwrap();

        assert_eq!(instructions[0].branch_target, None);
    }

    // Trait implementations

    #[test]
    fn test_resolved_instruction_traits() {
        let input = indoc! {"
            .Lloop:
                add x0, x0, #1
                b.lt .Lloop
        "};
        let asm = ParsedAssembly::parse(input);
        let instructions = asm.resolve().unwrap();

        // BasicInstruction trait
        assert_eq!(instructions[0].mnemonic(), "add");
        assert!(!instructions[0].is_branch());

        assert_eq!(instructions[1].mnemonic(), "b.lt");
        assert!(instructions[1].is_branch());
        assert!(instructions[1].is_conditional());

        // CfgInstruction trait
        assert_eq!(instructions[0].as_target(), 0);
        assert_eq!(instructions[1].as_target(), 1);
        assert_eq!(instructions[1].branch_target(), Some(0));
    }

    // Edge cases

    #[test]
    fn test_empty_label() {
        let line = parse_single_line(":");
        assert_eq!(line.label, Some(""));
    }

    #[test]
    fn test_unmatched_brackets() {
        // Extra closing brackets - doesn't panic
        let line = parse_single_line("    ldr x0, ]]]x1, x2");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.mnemonic, "ldr");

        // Unclosed opening bracket
        let line = parse_single_line("    ldr x0, [x1, x2");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.operands, vec!["x0", "[x1, x2"]);
    }

    #[test]
    fn test_unknown_mnemonic() {
        let line = parse_single_line("    asdfghjkl x0, x1, #999");
        let instruction = get_instruction(&line);
        assert_eq!(instruction.mnemonic, "asdfghjkl");
        assert!(!instruction.is_branch());
    }

    #[test]
    fn test_resolve_error_display() {
        let err = ResolveError::TrailingLabels(vec!["foo".into(), "bar".into()]);
        assert!(err.to_string().contains("foo"));
        assert!(err.to_string().contains("bar"));

        let err = ResolveError::UndefinedLabel {
            label: "missing".into(),
            line: 42,
        };
        assert!(err.to_string().contains("missing"));
        assert!(err.to_string().contains("42"));
    }
}
