//! Arm64 assembly text parser
//!
//! Parses GNU-style assembly syntax as produced by LLVM/GCC.

use std::fmt;

/// A parsed line from an assembly file
#[derive(Debug, Clone)]
pub struct ParsedLine {
    /// Label defined on this line (e.g., ".Lloop" from ".Lloop:")
    pub label: Option<String>,
    /// Instruction on this line
    pub instruction: Option<Instruction>,
    /// Directive on this line (e.g., ".global", ".align")
    pub directive: Option<Directive>,
    /// Original line number (1-indexed)
    pub line_number: usize,
    /// Original text (for reconstruction)
    pub original: String,
}

/// An assembly instruction
#[derive(Debug, Clone)]
pub struct Instruction {
    /// The mnemonic (e.g., "mov", "b.lt", "ret")
    pub mnemonic: String,
    /// Operands as strings (e.g., ["x0", "#0"])
    pub operands: Vec<String>,
}

impl Instruction {
    /// Check if an instruction is a return
    pub fn is_return(&self) -> bool {
        self.mnemonic.to_lowercase() == "ret"
    }

    /// Check if an instruction is a branch instruction
    pub fn is_branch(&self) -> bool {
        let mnemonic = self.mnemonic.to_lowercase();

        // Unconditional direct branches
        if mnemonic == "b" || mnemonic == "bl" {
            return true;
        }

        // Indirect branches (branch to register)
        // br xN  - unconditional indirect branch
        // blr xN - indirect branch with link (call through register)
        if mnemonic == "br" || mnemonic == "blr" {
            return true;
        }

        // Pointer authentication branch variants (ARMv8.3+)
        // braaz, brabz, blraaz, blrabz, etc.
        if mnemonic.starts_with("bra") || mnemonic.starts_with("blra") {
            return true;
        }

        // Conditional branches (b.eq, b.ne, b.lt, etc.)
        if mnemonic.starts_with("b.") {
            return true;
        }

        // Compare and branch
        if mnemonic == "cbz" || mnemonic == "cbnz" {
            return true;
        }

        // Test and branch
        if mnemonic == "tbz" || mnemonic == "tbnz" {
            return true;
        }

        false
    }

    /// Check if this is an indirect branch (target is a register, not a label)
    pub fn is_indirect_branch(&self) -> bool {
        let mnemonic = self.mnemonic.to_lowercase();
        mnemonic == "br"
            || mnemonic == "blr"
            || mnemonic.starts_with("bra")
            || mnemonic.starts_with("blra")
    }

    /// Check if a branch is conditional (can fall through)
    pub fn is_conditional_branch(&self) -> bool {
        let mnemonic = self.mnemonic.to_lowercase();

        // Conditional branches
        if mnemonic.starts_with("b.") {
            return true;
        }

        // Compare and branch
        if mnemonic == "cbz" || mnemonic == "cbnz" {
            return true;
        }

        // Test and branch
        if mnemonic == "tbz" || mnemonic == "tbnz" {
            return true;
        }

        false
    }

    /// Get the branch target label if this is a direct branch
    /// Returns None for indirect branches (br, blr) since target is a register
    pub fn get_branch_target(&self) -> Option<&str> {
        if !self.is_branch() || self.is_indirect_branch() {
            return None;
        }

        // For conditional branches like "b.lt .Lloop", the target is the last operand
        // For "b label" or "bl label", the target is the first/only operand
        // For "cbz x0, label" or "tbz x0, #bit, label", the target is the last operand
        self.operands.last().map(|s| s.as_str())
    }
}

/// An assembly directive
#[derive(Debug, Clone)]
pub struct Directive {
    /// The directive name without the leading dot (e.g., "global", "align")
    pub name: String,
    /// Arguments to the directive
    pub args: Vec<String>,
}

/// Parse error
#[derive(Debug)]
pub struct ParseError {
    pub line_number: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}: {}", self.line_number, self.message)
    }
}

impl std::error::Error for ParseError {}

pub struct Parser {}

impl Parser {
    /// Parse assembly text into a list of parsed lines
    pub fn parse(&self, input: &str) -> Result<Vec<ParsedLine>, ParseError> {
        let mut lines = Vec::new();

        for (idx, line_text) in input.lines().enumerate() {
            let line_number = idx + 1;
            let parsed = self.parse_line(line_text, line_number)?;
            lines.push(parsed);
        }

        Ok(lines)
    }

    /// Parse a single line of assembly
    fn parse_line(&self, line: &str, line_number: usize) -> Result<ParsedLine, ParseError> {
        let original = line.to_string();

        // Remove comments
        let line = self.remove_comments(line);
        // Trim whitespace
        let line = line.trim();

        // Empty line
        if line.is_empty() {
            return Ok(ParsedLine {
                label: None,
                instruction: None,
                directive: None,
                line_number,
                original,
            });
        }

        let mut label = None;
        let mut rest = line;

        // Check for label (ends with ':')
        if let Some(colon_pos) = self.find_label_colon(line) {
            label = Some(line[..colon_pos].trim().to_string());
            rest = line[colon_pos + 1..].trim();
        }

        // Empty after label
        if rest.is_empty() {
            return Ok(ParsedLine {
                label,
                instruction: None,
                directive: None,
                line_number,
                original,
            });
        }

        // Check for directive (starts with '.')
        if rest.starts_with('.') {
            let directive = self.parse_directive(rest)?;
            return Ok(ParsedLine {
                label,
                instruction: None,
                directive: Some(directive),
                line_number,
                original,
            });
        }

        // Otherwise it's an instruction
        let instruction = self.parse_instruction(rest)?;
        Ok(ParsedLine {
            label,
            instruction: Some(instruction),
            directive: None,
            line_number,
            original,
        })
    }

    /// Remove comments from a line
    /// Supports multiple comment styles:
    /// - // (C++ style)
    /// - /* */ (C style, single line only)
    /// - ; (traditional assembly style)
    /// - @ (GNU ARM assembler style)
    fn remove_comments<'a>(&self, line: &'a str) -> &'a str {
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
    fn find_label_colon(&self, line: &str) -> Option<usize> {
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

    /// Parse a directive line
    fn parse_directive(&self, line: &str) -> Result<Directive, ParseError> {
        // Skip the leading dot
        let line = &line[1..];

        // Split on whitespace
        let mut parts = line.split_whitespace();

        let name = parts.next().unwrap_or("").to_string();
        let args: Vec<String> = parts.map(|s| s.trim_end_matches(',').to_string()).collect();

        Ok(Directive { name, args })
    }

    /// Parse an instruction line
    fn parse_instruction(&self, line: &str) -> Result<Instruction, ParseError> {
        let line = line.trim();

        // Find mnemonic (first word, possibly with condition like "b.lt")
        let mut parts = line.splitn(2, |c: char| c.is_whitespace());

        let mnemonic = parts.next().unwrap_or("").to_string();
        let operands_str = parts.next().unwrap_or("");

        // Parse operands (comma-separated, but handle brackets)
        let operands = self.parse_operands(operands_str);

        Ok(Instruction { mnemonic, operands })
    }

    /// Parse comma-separated operands, handling brackets for addressing modes
    fn parse_operands(&self, s: &str) -> Vec<String> {
        let s = s.trim();
        if s.is_empty() {
            return Vec::new();
        }

        let mut operands = Vec::new();
        let mut current = String::new();
        let mut bracket_depth: i32 = 0;

        for c in s.chars() {
            match c {
                '[' => {
                    bracket_depth += 1;
                    current.push(c);
                }
                ']' => {
                    bracket_depth = bracket_depth.saturating_sub(1);
                    current.push(c);
                }
                ',' if bracket_depth == 0 => {
                    let trimmed = current.trim().to_string();
                    if !trimmed.is_empty() {
                        operands.push(trimmed);
                    }
                    current.clear();
                }
                _ => {
                    current.push(c);
                }
            }
        }

        // Don't forget the last operand
        let trimmed = current.trim().to_string();
        if !trimmed.is_empty() {
            operands.push(trimmed);
        }

        operands
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::Parser;

    #[test]
    fn test_parse_label() {
        let parser = Parser {};
        let lines = parser.parse(".Lloop:\n").unwrap();
        assert_eq!(lines[0].label, Some(".Lloop".to_string()));
        assert!(lines[0].instruction.is_none());
    }

    #[test]
    fn test_parse_instruction() {
        let parser = Parser {};
        let lines = parser.parse("    mov x0, #0\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "mov");
        assert_eq!(instr.operands, vec!["x0", "#0"]);
    }

    #[test]
    fn test_parse_directive() {
        let parser = Parser {};
        let lines = parser.parse(".global _test_loop\n").unwrap();
        let dir = lines[0].directive.as_ref().unwrap();
        assert_eq!(dir.name, "global");
        assert_eq!(dir.args, vec!["_test_loop"]);
    }

    #[test]
    fn test_parse_branch() {
        let parser = Parser {};
        let lines = parser.parse("    b.lt .Lloop\n").unwrap();
        let instruction = lines[0].instruction.as_ref().unwrap();
        assert!(instruction.is_branch());
        assert_eq!(instruction.get_branch_target(), Some(".Lloop"));
    }

    #[test]
    fn test_parse_label_with_instruction() {
        let parser = Parser {};
        let lines = parser.parse("_start: mov x0, #1\n").unwrap();
        assert_eq!(lines[0].label, Some("_start".to_string()));
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "mov");
    }

    #[test]
    fn test_parse_memory_operand() {
        let parser = Parser {};
        let lines = parser.parse("    ldr x0, [x1, #8]\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "ldr");
        assert_eq!(instr.operands, vec!["x0", "[x1, #8]"]);
    }

    #[test]
    fn test_indirect_branch_br() {
        let parser = Parser {};
        let lines = parser.parse("    br x0\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch(), "br should be recognized as a branch");
        assert!(
            instr.is_indirect_branch(),
            "br should be recognized as indirect"
        );
        assert!(
            !instr.is_conditional_branch(),
            "br should not be conditional"
        );
        assert_eq!(
            instr.get_branch_target(),
            None,
            "indirect branch has no static target"
        );
    }

    #[test]
    fn test_indirect_branch_blr() {
        let parser = Parser {};
        let lines = parser.parse("    blr x30\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch(), "blr should be recognized as a branch");
        assert!(
            instr.is_indirect_branch(),
            "blr should be recognized as indirect"
        );
        assert_eq!(
            instr.get_branch_target(),
            None,
            "indirect branch has no static target"
        );
    }

    #[test]
    fn test_direct_branch_has_target() {
        let parser = Parser {};

        // Direct unconditional branch
        let lines = parser.parse("    b .Llabel\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch());
        assert!(!instr.is_indirect_branch());
        assert_eq!(instr.get_branch_target(), Some(".Llabel"));

        // Direct branch with link (call)
        let lines = parser.parse("    bl _function\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch());
        assert!(!instr.is_indirect_branch());
        assert_eq!(instr.get_branch_target(), Some("_function"));
    }

    #[test]
    fn test_semicolon_comments() {
        let parser = Parser {};

        // Semicolon comment at end of line
        let lines = parser
            .parse("    mov x0, #0 ; initialize counter\n")
            .unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "mov");
        assert_eq!(instr.operands, vec!["x0", "#0"]);

        // Semicolon comment on its own line
        let lines = parser.parse("; this is a comment\n").unwrap();
        assert!(lines[0].instruction.is_none());
        assert!(lines[0].label.is_none());
    }

    #[test]
    fn test_at_sign_comments() {
        let parser = Parser {};

        // @ comment at end of line (GNU ARM assembler style)
        let lines = parser.parse("    add x0, x0, #1 @ increment\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "add");
        assert_eq!(instr.operands, vec!["x0", "x0", "#1"]);

        // @ comment on its own line
        let lines = parser.parse("@ GNU style comment\n").unwrap();
        assert!(lines[0].instruction.is_none());
    }

    #[test]
    fn test_cpp_style_comments() {
        let parser = Parser {};

        // // comment at end of line
        let lines = parser.parse("    ret // return to caller\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "ret");
    }

    #[test]
    fn test_c_style_comments() {
        let parser = Parser {};

        // /* */ comment at end of line
        let lines = parser.parse("    nop /* do nothing */\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "nop");
    }

    #[test]
    fn test_multiple_comment_styles_earliest_wins() {
        let parser = Parser {};

        // Semicolon appears before //
        let lines = parser
            .parse("    mov x0, #1 ; comment // not parsed\n")
            .unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.operands, vec!["x0", "#1"]);

        // // appears before ;
        let lines = parser
            .parse("    mov x0, #2 // comment ; not parsed\n")
            .unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.operands, vec!["x0", "#2"]);
    }

    #[test]
    fn test_is_return() {
        let parser = Parser {};
        let lines = parser.parse("    ret\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_return());
        assert!(!instr.is_branch());

        // Case insensitivity
        let lines = parser.parse("    RET\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_return());
    }

    #[test]
    fn test_cbz_cbnz_branches() {
        let parser = Parser {};

        // cbz - compare and branch if zero
        let lines = parser.parse("    cbz x0, .Lzero\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch(), "cbz should be a branch");
        assert!(instr.is_conditional_branch(), "cbz should be conditional");
        assert!(!instr.is_indirect_branch(), "cbz should not be indirect");
        assert_eq!(instr.get_branch_target(), Some(".Lzero"));

        // cbnz - compare and branch if not zero
        let lines = parser.parse("    cbnz w5, .Lnonzero\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch(), "cbnz should be a branch");
        assert!(instr.is_conditional_branch(), "cbnz should be conditional");
        assert_eq!(instr.get_branch_target(), Some(".Lnonzero"));
    }

    #[test]
    fn test_tbz_tbnz_branches() {
        let parser = Parser {};

        // tbz - test bit and branch if zero (3 operands)
        let lines = parser.parse("    tbz x0, #63, .Lpositive\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch(), "tbz should be a branch");
        assert!(instr.is_conditional_branch(), "tbz should be conditional");
        assert!(!instr.is_indirect_branch(), "tbz should not be indirect");
        assert_eq!(instr.get_branch_target(), Some(".Lpositive"));
        assert_eq!(instr.operands.len(), 3);

        // tbnz - test bit and branch if not zero
        let lines = parser.parse("    tbnz w1, #0, .Lodd\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch(), "tbnz should be a branch");
        assert!(instr.is_conditional_branch(), "tbnz should be conditional");
        assert_eq!(instr.get_branch_target(), Some(".Lodd"));
    }

    #[test]
    fn test_pac_branches() {
        let parser = Parser {};

        // braaz - branch to register with pointer authentication
        let lines = parser.parse("    braaz x0\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch(), "braaz should be a branch");
        assert!(instr.is_indirect_branch(), "braaz should be indirect");
        assert_eq!(instr.get_branch_target(), None);

        // blraaz - branch with link, pointer authentication
        let lines = parser.parse("    blraaz x1\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch(), "blraaz should be a branch");
        assert!(instr.is_indirect_branch(), "blraaz should be indirect");
    }

    #[test]
    fn test_label_with_directive() {
        let parser = Parser {};
        let lines = parser.parse("my_data: .quad 0x1234\n").unwrap();
        assert_eq!(lines[0].label, Some("my_data".to_string()));
        let dir = lines[0].directive.as_ref().unwrap();
        assert_eq!(dir.name, "quad");
        assert_eq!(dir.args, vec!["0x1234"]);
        assert!(lines[0].instruction.is_none());
    }

    #[test]
    fn test_empty_and_whitespace_lines() {
        let parser = Parser {};

        // Empty line
        let lines = parser.parse("\n").unwrap();
        assert!(lines[0].label.is_none());
        assert!(lines[0].instruction.is_none());
        assert!(lines[0].directive.is_none());

        // Whitespace only
        let lines = parser.parse("    \t  \n").unwrap();
        assert!(lines[0].label.is_none());
        assert!(lines[0].instruction.is_none());
    }

    #[test]
    fn test_multi_line_parsing() {
        let parser = Parser {};
        let input = ".global _start
_start:
    mov x0, #0
.Lloop:
    add x0, x0, #1
    cmp x0, #10
    b.lt .Lloop
    ret
";
        let lines = parser.parse(input).unwrap();
        assert_eq!(lines.len(), 8);

        // Check line numbers
        assert_eq!(lines[0].line_number, 1);
        assert_eq!(lines[1].line_number, 2);
        assert_eq!(lines[7].line_number, 8);

        // Check content
        assert!(lines[0].directive.is_some()); // .global
        assert_eq!(lines[1].label, Some("_start".to_string()));
        assert_eq!(lines[3].label, Some(".Lloop".to_string()));
        assert!(lines[7].instruction.as_ref().unwrap().is_return());
    }

    #[test]
    fn test_original_field_preserves_comments() {
        let parser = Parser {};
        let input = "    mov x0, #0 ; this is a comment\n";
        let lines = parser.parse(input).unwrap();
        assert_eq!(lines[0].original, "    mov x0, #0 ; this is a comment");
    }

    #[test]
    fn test_post_index_addressing() {
        let parser = Parser {};
        // Post-indexed: ldr x0, [x1], #8 - comma is outside brackets
        let lines = parser.parse("    ldr x0, [x1], #8\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "ldr");
        assert_eq!(instr.operands, vec!["x0", "[x1]", "#8"]);
    }

    #[test]
    fn test_pre_index_writeback() {
        let parser = Parser {};
        // Pre-indexed with writeback: ldr x0, [x1, #8]!
        let lines = parser.parse("    ldr x0, [x1, #8]!\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "ldr");
        assert_eq!(instr.operands, vec!["x0", "[x1, #8]!"]);
    }

    #[test]
    fn test_case_insensitivity_branches() {
        let parser = Parser {};

        // Uppercase
        let lines = parser.parse("    B.LT .Lloop\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch());
        assert!(instr.is_conditional_branch());

        // Mixed case
        let lines = parser.parse("    Cbz x0, .Lzero\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch());
    }

    #[test]
    fn test_non_branch_non_return() {
        let parser = Parser {};
        let lines = parser.parse("    add x0, x1, x2\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(!instr.is_branch());
        assert!(!instr.is_return());
        assert!(!instr.is_conditional_branch());
        assert!(!instr.is_indirect_branch());
        assert_eq!(instr.get_branch_target(), None);
    }

    #[test]
    fn test_bl_is_unconditional() {
        let parser = Parser {};
        let lines = parser.parse("    bl _function\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch());
        assert!(
            !instr.is_conditional_branch(),
            "bl is a call, not conditional"
        );
    }

    #[test]
    fn test_instruction_no_operands() {
        let parser = Parser {};

        let lines = parser.parse("    ret\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "ret");
        assert!(instr.operands.is_empty());

        let lines = parser.parse("    nop\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "nop");
        assert!(instr.operands.is_empty());
    }

    #[test]
    fn test_label_with_dollar_sign() {
        let parser = Parser {};
        let lines = parser.parse("$Lfoo$bar:\n").unwrap();
        assert_eq!(lines[0].label, Some("$Lfoo$bar".to_string()));
    }

    #[test]
    fn test_all_conditional_branch_variants() {
        let parser = Parser {};
        let conditions = [
            "b.eq", "b.ne", "b.cs", "b.cc", "b.mi", "b.pl", "b.vs", "b.vc", "b.hi", "b.ls", "b.ge",
            "b.lt", "b.gt", "b.le", "b.al",
        ];

        for cond in conditions {
            let input = format!("    {} .Ltarget\n", cond);
            let lines = parser.parse(&input).unwrap();
            let instr = lines[0].instruction.as_ref().unwrap();
            assert!(instr.is_branch(), "{} should be a branch", cond);
            assert!(
                instr.is_conditional_branch(),
                "{} should be conditional",
                cond
            );
            assert_eq!(instr.get_branch_target(), Some(".Ltarget"));
        }
    }

    #[test]
    fn test_ldp_stp_pair_operations() {
        let parser = Parser {};

        // Load pair
        let lines = parser.parse("    ldp x0, x1, [sp, #16]\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "ldp");
        assert_eq!(instr.operands, vec!["x0", "x1", "[sp, #16]"]);

        // Store pair
        let lines = parser.parse("    stp x29, x30, [sp, #-16]!\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "stp");
        assert_eq!(instr.operands, vec!["x29", "x30", "[sp, #-16]!"]);
    }
}
