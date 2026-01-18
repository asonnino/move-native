//! Arm64 assembly text parser
//!
//! Parses GNU-style assembly syntax as produced by LLVM/GCC.

use std::collections::HashMap;

use cfg::InstructionInfo;

/// Error during label resolution
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolveError {
    /// Labels at end of file with no following instruction
    TrailingLabels(Vec<String>),
    /// Branch references an undefined label
    UndefinedLabel { label: String, line: usize },
}

impl std::fmt::Display for ResolveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResolveError::TrailingLabels(labels) => {
                write!(f, "trailing labels with no instruction: {labels:?}")
            }
            ResolveError::UndefinedLabel { label, line } => {
                write!(f, "undefined label '{label}' referenced at line {line}",)
            }
        }
    }
}

impl std::error::Error for ResolveError {}

/// A resolved instruction with all labels resolved to instruction indices.
///
/// This is the output of the resolution pass. Every item represents an actual
/// CPU instruction (no label-only lines or directives).
#[derive(Debug, Clone)]
pub struct ResolvedInstruction {
    /// Index in the instruction stream (0-based)
    pub index: usize,
    /// The mnemonic (always present)
    pub mnemonic: String,
    /// Branch target as instruction index (if this is a branch)
    pub branch_target: Option<usize>,
    /// Original line number (1-indexed, for error messages and output mapping)
    pub line_number: usize,
}

impl InstructionInfo for ResolvedInstruction {
    fn mnemonic(&self) -> &str {
        &self.mnemonic
    }

    fn branch_target(&self) -> Option<usize> {
        self.branch_target
    }

    fn as_target(&self) -> usize {
        self.index
    }
}

/// A parsed line from an assembly file
pub struct ParsedLine<'a> {
    /// Label defined on this line (e.g., ".Lloop" from ".Lloop:")
    pub label: Option<&'a str>,
    /// The statement on this line (instruction, directive, or empty)
    pub statement: Statement<'a>,
    /// Original line number (1-indexed)
    pub line_number: usize,
    /// Original text (for reconstruction)
    pub original: &'a str,
}

/// The content of an assembly line after any label
pub enum Statement<'a> {
    /// A CPU instruction
    Instruction(UnresolvedInstruction<'a>),
    /// An assembler directive (e.g., .global, .align) - contents not parsed
    Directive,
    /// Empty line or label-only
    Empty,
}

/// An assembly instruction
pub struct UnresolvedInstruction<'a> {
    /// The mnemonic (e.g., "mov", "b.lt", "ret")
    pub mnemonic: &'a str,
    /// Operands as strings (e.g., ["x0", "#0"])
    pub operands: Vec<&'a str>,
}

impl<'a> UnresolvedInstruction<'a> {
    /// Parse an instruction from a line of text
    fn parse(line: &'a str) -> Self {
        let line = line.trim();

        // Find mnemonic (first word, possibly with condition like "b.lt")
        let mut parts = line.splitn(2, |c: char| c.is_whitespace());

        let mnemonic = parts.next().unwrap_or("");
        let operands_str = parts.next().unwrap_or("");

        // Parse operands (comma-separated, but handle brackets)
        let operands = Self::parse_operands(operands_str);

        Self { mnemonic, operands }
    }

    /// Parse comma-separated operands, handling brackets for addressing modes
    fn parse_operands(s: &'a str) -> Vec<&'a str> {
        let s = s.trim();
        if s.is_empty() {
            return Vec::new();
        }

        let mut operands = Vec::new();
        let mut start = 0;
        let mut bracket_depth: i32 = 0;

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

        // Don't forget the last operand
        let operand = s[start..].trim();
        if !operand.is_empty() {
            operands.push(operand);
        }

        operands
    }
}

impl UnresolvedInstruction<'_> {
    fn mnemonic_eq(&self, s: &str) -> bool {
        self.mnemonic.eq_ignore_ascii_case(s)
    }

    fn mnemonic_starts_with(&self, prefix: &str) -> bool {
        // Use get() to avoid panicking on multi-byte UTF-8 boundaries
        self.mnemonic
            .get(..prefix.len())
            .is_some_and(|s| s.eq_ignore_ascii_case(prefix))
    }

    fn is_branch(&self) -> bool {
        // Unconditional direct branches
        self.mnemonic_eq("b")
            || self.mnemonic_eq("bl")
            // Indirect branches (branch to register)
            || self.mnemonic_eq("br")
            || self.mnemonic_eq("blr")
            // Pointer authentication branch variants (ARMv8.3+)
            || self.mnemonic_starts_with("bra")
            || self.mnemonic_starts_with("blra")
            // Conditional branches (b.eq, b.ne, b.lt, etc.)
            || self.mnemonic_starts_with("b.")
            // Compare and branch
            || self.mnemonic_eq("cbz")
            || self.mnemonic_eq("cbnz")
            // Test and branch
            || self.mnemonic_eq("tbz")
            || self.mnemonic_eq("tbnz")
    }

    fn is_indirect_branch(&self) -> bool {
        self.mnemonic_eq("br")
            || self.mnemonic_eq("blr")
            || self.mnemonic_starts_with("bra")
            || self.mnemonic_starts_with("blra")
    }

    /// Get the branch target label if this is a direct branch.
    /// Returns None for indirect branches (br, blr) since target is a register.
    fn get_branch_target(&self) -> Option<&str> {
        if !self.is_branch() || self.is_indirect_branch() {
            return None;
        }
        self.operands.last().copied()
    }
}

/// Parsed assembly text, ready for resolution or instrumentation.
pub struct ParsedAssembly<'a> {
    lines: Vec<ParsedLine<'a>>,
}

impl<'a> ParsedAssembly<'a> {
    /// Parse assembly text.
    pub fn parse(input: &'a str) -> Self {
        let lines = input
            .lines()
            .enumerate()
            .map(|(idx, line_text)| Self::parse_line(line_text, idx + 1))
            .collect();
        Self { lines }
    }

    /// Resolve labels to instruction indices.
    ///
    /// This function:
    /// 1. Filters to only actual instructions (skips labels-only, directives, empty lines)
    /// 2. Maps labels to the index of the first instruction at or after them
    /// 3. Resolves branch target labels to instruction indices
    ///
    /// Returns a clean instruction stream where every item is an instruction with
    /// resolved branch targets.
    pub fn resolve(&self) -> Result<Vec<ResolvedInstruction>, ResolveError> {
        // First pass: build instructions with None branch_target, track labels separately
        let mut instructions: Vec<ResolvedInstruction> = Vec::new();
        let mut branch_labels: Vec<Option<&str>> = Vec::new(); // parallel to instructions
        let mut pending_labels: Vec<&str> = Vec::new();
        let mut label_to_index: HashMap<&str, usize> = HashMap::new();

        for line in &self.lines {
            // Accumulate any labels we encounter
            if let Some(label) = line.label {
                pending_labels.push(label);
            }

            // When we hit an instruction, all pending labels resolve to it
            if let Statement::Instruction(ref instruction) = line.statement {
                let index = instructions.len();

                for label in pending_labels.drain(..) {
                    label_to_index.insert(label, index);
                }

                instructions.push(ResolvedInstruction {
                    index,
                    mnemonic: instruction.mnemonic.to_string(),
                    branch_target: None, // resolved in second pass
                    line_number: line.line_number,
                });
                branch_labels.push(instruction.get_branch_target());
            }
            // Directives and empty: skip, but labels before them stay pending
        }

        // Trailing labels with no following instruction
        if !pending_labels.is_empty() {
            return Err(ResolveError::TrailingLabels(
                pending_labels.into_iter().map(String::from).collect(),
            ));
        }

        // Second pass: resolve branch targets in place
        for (instruction, label) in instructions.iter_mut().zip(branch_labels.iter()) {
            if let Some(label) = label {
                let target =
                    label_to_index
                        .get(label)
                        .copied()
                        .ok_or_else(|| ResolveError::UndefinedLabel {
                            label: label.to_string(),
                            line: instruction.line_number,
                        })?;
                instruction.branch_target = Some(target);
            }
        }

        Ok(instructions)
    }

    /// Access the parsed lines.
    pub fn lines(&self) -> &[ParsedLine<'a>] {
        &self.lines
    }

    /// Parse a single line of assembly
    fn parse_line(line: &'a str, line_number: usize) -> ParsedLine<'a> {
        let original = line;

        // Remove comments
        let line = Self::remove_comments(line);
        // Trim whitespace
        let line = line.trim();

        // Empty line
        if line.is_empty() {
            return ParsedLine {
                label: None,
                statement: Statement::Empty,
                line_number,
                original,
            };
        }

        let mut label = None;
        let mut rest = line;

        // Check for label (ends with ':')
        if let Some(colon_position) = Self::find_label_colon(line) {
            label = Some(line[..colon_position].trim());
            rest = line[colon_position + 1..].trim();
        }

        // Empty after label
        if rest.is_empty() {
            return ParsedLine {
                label,
                statement: Statement::Empty,
                line_number,
                original,
            };
        }

        // Check for directive (starts with '.')
        if rest.starts_with('.') {
            return ParsedLine {
                label,
                statement: Statement::Directive,
                line_number,
                original,
            };
        }

        // Otherwise it's an instruction
        ParsedLine {
            label,
            statement: Statement::Instruction(UnresolvedInstruction::parse(rest)),
            line_number,
            original,
        }
    }

    /// Remove comments from a line
    /// Supports multiple comment styles:
    /// - // (C++ style)
    /// - /* */ (C style, single line only)
    /// - ; (traditional assembly style)
    /// - @ (GNU ARM assembler style)
    fn remove_comments(line: &str) -> &str {
        // Find the earliest comment start position
        let mut earliest_pos = line.len();

        // C++ style comments
        if let Some(pos) = line.find("//") {
            earliest_pos = earliest_pos.min(pos);
        }

        // C style comments (simplified - assumes single line)
        if let Some(pos) = line.find("/*") {
            earliest_pos = earliest_pos.min(pos);
        }

        // Traditional assembly semicolon comments
        if let Some(pos) = line.find(';') {
            earliest_pos = earliest_pos.min(pos);
        }

        // GNU ARM assembler @ comments
        if let Some(pos) = line.find('@') {
            earliest_pos = earliest_pos.min(pos);
        }

        &line[..earliest_pos]
    }

    /// Find the position of a label-ending colon
    /// Labels can contain alphanumeric chars, underscores, dots, and $
    fn find_label_colon(line: &str) -> Option<usize> {
        let mut chars = line.char_indices().peekable();

        // Skip leading whitespace
        while let Some(&(_, c)) = chars.peek() {
            if !c.is_whitespace() {
                break;
            }
            chars.next();
        }

        // Collect label characters
        while let Some((pos, c)) = chars.next() {
            if c == ':' {
                return Some(pos);
            }
            // Valid label characters
            if c.is_alphanumeric() || c == '_' || c == '.' || c == '$' {
                continue;
            }
            // Hit something else (like whitespace or instruction)
            break;
        }

        None
    }
}

// #[cfg(test)]
// mod tests {
//     use indoc::indoc;

//     use super::parse;

//     #[test]
//     fn test_parse_label() {
//         let lines = parse(".Lloop:\n");
//         assert_eq!(lines[0].label, Some(".Lloop"));
//         assert!(lines[0].instruction.is_none());
//     }

//     #[test]
//     fn test_parse_instruction() {
//         let lines = parse("    mov x0, #0\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.mnemonic, "mov");
//         assert_eq!(instr.operands, vec!["x0", "#0"]);
//     }

//     #[test]
//     fn test_parse_directive() {
//         let lines = parse(".global _test_loop\n");
//         let dir = lines[0].directive.as_ref().unwrap();
//         assert_eq!(dir.name, "global");
//         assert_eq!(dir.args, vec!["_test_loop"]);
//     }

//     #[test]
//     fn test_parse_branch() {
//         let lines = parse("    b.lt .Lloop\n");
//         let instruction = lines[0].instruction.as_ref().unwrap();
//         assert!(instruction.is_branch());
//         assert_eq!(instruction.get_branch_target(), Some(".Lloop"));
//     }

//     #[test]
//     fn test_parse_label_with_instruction() {
//         let lines = parse("_start: mov x0, #1\n");
//         assert_eq!(lines[0].label, Some("_start"));
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.mnemonic, "mov");
//     }

//     #[test]
//     fn test_parse_memory_operand() {
//         let lines = parse("    ldr x0, [x1, #8]\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.mnemonic, "ldr");
//         assert_eq!(instr.operands, vec!["x0", "[x1, #8]"]);
//     }

//     #[test]
//     fn test_indirect_branch_br() {
//         let lines = parse("    br x0\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert!(instr.is_branch(), "br should be recognized as a branch");
//         assert!(
//             instr.is_indirect_branch(),
//             "br should be recognized as indirect"
//         );
//         assert!(
//             !instr.is_conditional_branch(),
//             "br should not be conditional"
//         );
//         assert_eq!(
//             instr.get_branch_target(),
//             None,
//             "indirect branch has no static target"
//         );
//     }

//     #[test]
//     fn test_indirect_branch_blr() {
//         let lines = parse("    blr x30\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert!(instr.is_branch(), "blr should be recognized as a branch");
//         assert!(
//             instr.is_indirect_branch(),
//             "blr should be recognized as indirect"
//         );
//         assert_eq!(
//             instr.get_branch_target(),
//             None,
//             "indirect branch has no static target"
//         );
//     }

//     #[test]
//     fn test_direct_branch_has_target() {
//         // Direct unconditional branch
//         let lines = parse("    b .Llabel\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert!(instr.is_branch());
//         assert!(!instr.is_indirect_branch());
//         assert_eq!(instr.get_branch_target(), Some(".Llabel"));

//         // Direct branch with link (call)
//         let lines = parse("    bl _function\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert!(instr.is_branch());
//         assert!(!instr.is_indirect_branch());
//         assert_eq!(instr.get_branch_target(), Some("_function"));
//     }

//     #[test]
//     fn test_semicolon_comments() {
//         // Semicolon comment at end of line
//         let lines = parse("    mov x0, #0 ; initialize counter\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.mnemonic, "mov");
//         assert_eq!(instr.operands, vec!["x0", "#0"]);

//         // Semicolon comment on its own line
//         let lines = parse("; this is a comment\n");
//         assert!(lines[0].instruction.is_none());
//         assert!(lines[0].label.is_none());
//     }

//     #[test]
//     fn test_at_sign_comments() {
//         // @ comment at end of line (GNU ARM assembler style)
//         let lines = parse("    add x0, x0, #1 @ increment\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.mnemonic, "add");
//         assert_eq!(instr.operands, vec!["x0", "x0", "#1"]);

//         // @ comment on its own line
//         let lines = parse("@ GNU style comment\n");
//         assert!(lines[0].instruction.is_none());
//     }

//     #[test]
//     fn test_cpp_style_comments() {
//         // // comment at end of line
//         let lines = parse("    ret // return to caller\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.mnemonic, "ret");
//     }

//     #[test]
//     fn test_c_style_comments() {
//         // /* */ comment at end of line
//         let lines = parse("    nop /* do nothing */\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.mnemonic, "nop");
//     }

//     #[test]
//     fn test_multiple_comment_styles_earliest_wins() {
//         // Semicolon appears before //
//         let lines = parse("    mov x0, #1 ; comment // not parsed\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.operands, vec!["x0", "#1"]);

//         // // appears before ;
//         let lines = parse("    mov x0, #2 // comment ; not parsed\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.operands, vec!["x0", "#2"]);
//     }

//     #[test]
//     fn test_is_return() {
//         let lines = parse("    ret\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert!(instr.is_return());
//         assert!(!instr.is_branch());

//         // Case insensitivity
//         let lines = parse("    RET\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert!(instr.is_return());
//     }

//     #[test]
//     fn test_cbz_cbnz_branches() {
//         // cbz - compare and branch if zero
//         let lines = parse("    cbz x0, .Lzero\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert!(instr.is_branch(), "cbz should be a branch");
//         assert!(instr.is_conditional_branch(), "cbz should be conditional");
//         assert!(!instr.is_indirect_branch(), "cbz should not be indirect");
//         assert_eq!(instr.get_branch_target(), Some(".Lzero"));

//         // cbnz - compare and branch if not zero
//         let lines = parse("    cbnz w5, .Lnonzero\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert!(instr.is_branch(), "cbnz should be a branch");
//         assert!(instr.is_conditional_branch(), "cbnz should be conditional");
//         assert_eq!(instr.get_branch_target(), Some(".Lnonzero"));
//     }

//     #[test]
//     fn test_tbz_tbnz_branches() {
//         // tbz - test bit and branch if zero (3 operands)
//         let lines = parse("    tbz x0, #63, .Lpositive\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert!(instr.is_branch(), "tbz should be a branch");
//         assert!(instr.is_conditional_branch(), "tbz should be conditional");
//         assert!(!instr.is_indirect_branch(), "tbz should not be indirect");
//         assert_eq!(instr.get_branch_target(), Some(".Lpositive"));
//         assert_eq!(instr.operands.len(), 3);

//         // tbnz - test bit and branch if not zero
//         let lines = parse("    tbnz w1, #0, .Lodd\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert!(instr.is_branch(), "tbnz should be a branch");
//         assert!(instr.is_conditional_branch(), "tbnz should be conditional");
//         assert_eq!(instr.get_branch_target(), Some(".Lodd"));
//     }

//     #[test]
//     fn test_pac_branches() {
//         // braaz - branch to register with pointer authentication
//         let lines = parse("    braaz x0\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert!(instr.is_branch(), "braaz should be a branch");
//         assert!(instr.is_indirect_branch(), "braaz should be indirect");
//         assert_eq!(instr.get_branch_target(), None);

//         // blraaz - branch with link, pointer authentication
//         let lines = parse("    blraaz x1\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert!(instr.is_branch(), "blraaz should be a branch");
//         assert!(instr.is_indirect_branch(), "blraaz should be indirect");
//     }

//     #[test]
//     fn test_label_with_directive() {
//         let lines = parse("my_data: .quad 0x1234\n");
//         assert_eq!(lines[0].label, Some("my_data"));
//         let dir = lines[0].directive.as_ref().unwrap();
//         assert_eq!(dir.name, "quad");
//         assert_eq!(dir.args, vec!["0x1234"]);
//         assert!(lines[0].instruction.is_none());
//     }

//     #[test]
//     fn test_empty_and_whitespace_lines() {
//         // Empty line
//         let lines = parse("\n");
//         assert!(lines[0].label.is_none());
//         assert!(lines[0].instruction.is_none());
//         assert!(lines[0].directive.is_none());

//         // Whitespace only
//         let lines = parse("    \t  \n");
//         assert!(lines[0].label.is_none());
//         assert!(lines[0].instruction.is_none());
//     }

//     #[test]
//     fn test_multi_line_parsing() {
//         let input = indoc! {"
//             .global _start
//             _start:
//                 mov x0, #0
//             .Lloop:
//                 add x0, x0, #1
//                 cmp x0, #10
//                 b.lt .Lloop
//                 ret
//         "};
//         let lines = parse(input);
//         assert_eq!(lines.len(), 8);

//         // Check line numbers
//         assert_eq!(lines[0].line_number, 1);
//         assert_eq!(lines[1].line_number, 2);
//         assert_eq!(lines[7].line_number, 8);

//         // Check content
//         assert!(lines[0].directive.is_some()); // .global
//         assert_eq!(lines[1].label, Some("_start"));
//         assert_eq!(lines[3].label, Some(".Lloop"));
//         assert!(lines[7].instruction.as_ref().unwrap().is_return());
//     }

//     #[test]
//     fn test_original_field_preserves_comments() {
//         let input = "    mov x0, #0 ; this is a comment\n";
//         let lines = parse(input);
//         assert_eq!(lines[0].original, "    mov x0, #0 ; this is a comment");
//     }

//     #[test]
//     fn test_post_index_addressing() {
//         // Post-indexed: ldr x0, [x1], #8 - comma is outside brackets
//         let lines = parse("    ldr x0, [x1], #8\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.mnemonic, "ldr");
//         assert_eq!(instr.operands, vec!["x0", "[x1]", "#8"]);
//     }

//     #[test]
//     fn test_pre_index_writeback() {
//         // Pre-indexed with writeback: ldr x0, [x1, #8]!
//         let lines = parse("    ldr x0, [x1, #8]!\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.mnemonic, "ldr");
//         assert_eq!(instr.operands, vec!["x0", "[x1, #8]!"]);
//     }

//     #[test]
//     fn test_case_insensitivity_branches() {
//         // Uppercase
//         let lines = parse("    B.LT .Lloop\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert!(instr.is_branch());
//         assert!(instr.is_conditional_branch());

//         // Mixed case
//         let lines = parse("    Cbz x0, .Lzero\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert!(instr.is_branch());
//     }

//     #[test]
//     fn test_non_branch_non_return() {
//         let lines = parse("    add x0, x1, x2\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert!(!instr.is_branch());
//         assert!(!instr.is_return());
//         assert!(!instr.is_conditional_branch());
//         assert!(!instr.is_indirect_branch());
//         assert_eq!(instr.get_branch_target(), None);
//     }

//     #[test]
//     fn test_bl_is_unconditional() {
//         let lines = parse("    bl _function\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert!(instr.is_branch());
//         assert!(
//             !instr.is_conditional_branch(),
//             "bl is a call, not conditional"
//         );
//     }

//     #[test]
//     fn test_instruction_no_operands() {
//         let lines = parse("    ret\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.mnemonic, "ret");
//         assert!(instr.operands.is_empty());

//         let lines = parse("    nop\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.mnemonic, "nop");
//         assert!(instr.operands.is_empty());
//     }

//     #[test]
//     fn test_label_with_dollar_sign() {
//         let lines = parse("$Lfoo$bar:\n");
//         assert_eq!(lines[0].label, Some("$Lfoo$bar"));
//     }

//     #[test]
//     fn test_all_conditional_branch_variants() {
//         let conditions = [
//             "b.eq", "b.ne", "b.cs", "b.cc", "b.mi", "b.pl", "b.vs", "b.vc", "b.hi", "b.ls", "b.ge",
//             "b.lt", "b.gt", "b.le", "b.al",
//         ];

//         for cond in conditions {
//             let input = format!("    {} .Ltarget\n", cond);
//             let lines = parse(&input);
//             let instr = lines[0].instruction.as_ref().unwrap();
//             assert!(instr.is_branch(), "{} should be a branch", cond);
//             assert!(
//                 instr.is_conditional_branch(),
//                 "{} should be conditional",
//                 cond
//             );
//             assert_eq!(instr.get_branch_target(), Some(".Ltarget"));
//         }
//     }

//     #[test]
//     fn test_ldp_stp_pair_operations() {
//         // Load pair
//         let lines = parse("    ldp x0, x1, [sp, #16]\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.mnemonic, "ldp");
//         assert_eq!(instr.operands, vec!["x0", "x1", "[sp, #16]"]);

//         // Store pair
//         let lines = parse("    stp x29, x30, [sp, #-16]!\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.mnemonic, "stp");
//         assert_eq!(instr.operands, vec!["x29", "x30", "[sp, #-16]!"]);
//     }

//     #[test]
//     fn test_malformed_empty_mnemonic() {
//         // Just a colon - creates empty label, no instruction
//         let lines = parse(":\n");
//         assert_eq!(lines[0].label, Some(""));
//         assert!(lines[0].instruction.is_none());

//         // Whitespace then colon - still finds the colon as label end
//         let lines = parse("   :\n");
//         assert_eq!(lines[0].label, Some("")); // empty label after trimming
//     }

//     #[test]
//     fn test_malformed_multiple_colons() {
//         let lines = parse("foo:::\n");
//         // First colon ends the label, rest is parsed as instruction
//         assert_eq!(lines[0].label, Some("foo"));
//         assert!(lines[0].instruction.is_some());
//         assert_eq!(lines[0].instruction.as_ref().unwrap().mnemonic, "::");
//     }

//     #[test]
//     fn test_malformed_unmatched_brackets() {
//         // Extra closing brackets - doesn't panic due to saturating_sub
//         let lines = parse("    ldr x0, ]]]x1, x2\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.mnemonic, "ldr");
//         // Parser handles this gracefully (exact output doesn't matter, just no panic)
//         assert!(!instr.operands.is_empty());

//         // Unclosed opening brackets - comma inside isn't a separator
//         let lines = parse("    ldr x0, [x1, x2\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         // The entire "[x1, x2" is one operand because bracket never closed
//         assert_eq!(instr.operands, vec!["x0", "[x1, x2"]);
//     }

//     #[test]
//     fn test_malformed_unicode_and_emoji() {
//         // Emoji is not a valid label char (only alphanumeric, _, ., $)
//         // So "🔥:" is parsed as instruction "🔥:" with no label
//         let lines = parse("🔥:\n");
//         assert!(lines[0].label.is_none());
//         assert!(lines[0].instruction.is_some());
//         assert_eq!(lines[0].instruction.as_ref().unwrap().mnemonic, "🔥:");

//         // Unicode letters ARE alphanumeric, so they work in instructions
//         let lines = parse("    日本語 x0, x1\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.mnemonic, "日本語");
//     }

//     #[test]
//     fn test_malformed_only_whitespace_and_comments() {
//         let lines = parse("    ; just a comment\n");
//         assert!(lines[0].instruction.is_none());
//         assert!(lines[0].label.is_none());

//         let lines = parse("    \t   \n");
//         assert!(lines[0].instruction.is_none());
//     }

//     #[test]
//     fn test_malformed_directive_edge_cases() {
//         // Just a dot
//         let lines = parse(".\n");
//         let dir = lines[0].directive.as_ref().unwrap();
//         assert_eq!(dir.name, "");
//         assert!(dir.args.is_empty());

//         // Dot with spaces but no name
//         let lines = parse(".   \n");
//         let dir = lines[0].directive.as_ref().unwrap();
//         assert_eq!(dir.name, "");
//     }

//     #[test]
//     fn test_malformed_nonsense_mnemonic() {
//         // Completely made up instruction - parser doesn't validate
//         let lines = parse("    asdfghjkl x0, x1, #999\n");
//         let instr = lines[0].instruction.as_ref().unwrap();
//         assert_eq!(instr.mnemonic, "asdfghjkl");
//         assert!(!instr.is_branch());
//         assert!(!instr.is_return());
//     }
// }
