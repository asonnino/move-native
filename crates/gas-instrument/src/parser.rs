//! Arm64 assembly text parser
//!
//! Parses GNU-style assembly syntax as produced by LLVM/GCC.

use std::fmt;

/// A parsed line from an assembly file
pub struct ParsedLine<'a> {
    /// Label defined on this line (e.g., ".Lloop" from ".Lloop:")
    pub label: Option<&'a str>,
    /// Instruction on this line
    pub instruction: Option<Instruction<'a>>,
    /// Directive on this line (e.g., ".global", ".align")
    pub directive: Option<Directive<'a>>,
    /// Original line number (1-indexed)
    pub line_number: usize,
    /// Original text (for reconstruction)
    pub original: &'a str,
}

/// An assembly instruction
pub struct Instruction<'a> {
    /// The mnemonic (e.g., "mov", "b.lt", "ret")
    pub mnemonic: &'a str,
    /// Operands as strings (e.g., ["x0", "#0"])
    pub operands: Vec<&'a str>,
}

impl Instruction<'_> {
    /// Case-insensitive check if mnemonic equals the given string
    fn mnemonic_eq(&self, s: &str) -> bool {
        self.mnemonic.eq_ignore_ascii_case(s)
    }

    /// Case-insensitive check if mnemonic starts with the given prefix
    fn mnemonic_starts_with(&self, prefix: &str) -> bool {
        self.mnemonic.len() >= prefix.len()
            && self.mnemonic[..prefix.len()].eq_ignore_ascii_case(prefix)
    }

    /// Check if an instruction is a return
    pub fn is_return(&self) -> bool {
        self.mnemonic_eq("ret")
    }

    /// Check if an instruction is a branch instruction
    pub fn is_branch(&self) -> bool {
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

    /// Check if this is an indirect branch (target is a register, not a label)
    pub fn is_indirect_branch(&self) -> bool {
        self.mnemonic_eq("br")
            || self.mnemonic_eq("blr")
            || self.mnemonic_starts_with("bra")
            || self.mnemonic_starts_with("blra")
    }

    /// Check if this is a call instruction (branch with link).
    /// Calls save a return address and expect the callee to return.
    pub fn is_call(&self) -> bool {
        self.mnemonic_eq("bl") || self.mnemonic_eq("blr") || self.mnemonic_starts_with("blra")
    }

    /// Check if this is an unconditional jump (no fall-through, no return).
    /// These transfer control permanently without saving a return address.
    pub fn is_unconditional_jump(&self) -> bool {
        self.mnemonic_eq("b") || self.mnemonic_eq("br") || self.mnemonic_starts_with("bra")
    }

    /// Check if a branch is conditional (can fall through)
    pub fn is_conditional_branch(&self) -> bool {
        // Conditional branches
        self.mnemonic_starts_with("b.")
            // Compare and branch
            || self.mnemonic_eq("cbz")
            || self.mnemonic_eq("cbnz")
            // Test and branch
            || self.mnemonic_eq("tbz")
            || self.mnemonic_eq("tbnz")
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
        self.operands.last().copied()
    }
}

/// An assembly directive
pub struct Directive<'a> {
    /// The directive name without the leading dot (e.g., "global", "align")
    pub name: &'a str,
    /// Arguments to the directive
    pub args: Vec<&'a str>,
}

/// Parse error
#[derive(Debug)]
pub struct ParseError {
    pub line_number: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "line {}: {}", self.line_number, self.message)
    }
}

impl std::error::Error for ParseError {}

/// Parse assembly text into a list of parsed lines
pub fn parse(input: &str) -> Result<Vec<ParsedLine>, ParseError> {
    Parser::new(input).parse()
}

struct Parser<'a> {
    input: &'a str,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Self { input }
    }

    /// Parse assembly text into a list of parsed lines
    fn parse(&self) -> Result<Vec<ParsedLine<'a>>, ParseError> {
        let mut lines = Vec::new();

        for (idx, line_text) in self.input.lines().enumerate() {
            let line_number = idx + 1;
            let parsed = self.parse_line(line_text, line_number)?;
            lines.push(parsed);
        }

        Ok(lines)
    }

    /// Parse a single line of assembly
    fn parse_line(&self, line: &'a str, line_number: usize) -> Result<ParsedLine<'a>, ParseError> {
        let original = line;

        // Remove comments
        let line = remove_comments(line);
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
        if let Some(colon_pos) = find_label_colon(line) {
            label = Some(line[..colon_pos].trim());
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
            let directive = parse_directive(rest)?;
            return Ok(ParsedLine {
                label,
                instruction: None,
                directive: Some(directive),
                line_number,
                original,
            });
        }

        // Otherwise it's an instruction
        let instruction = parse_instruction(rest)?;
        Ok(ParsedLine {
            label,
            instruction: Some(instruction),
            directive: None,
            line_number,
            original,
        })
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

/// Parse a directive line
fn parse_directive(line: &str) -> Result<Directive, ParseError> {
    // Skip the leading dot
    let line = &line[1..];

    // Split on whitespace
    let mut parts = line.split_whitespace();

    let name = parts.next().unwrap_or("");
    let args: Vec<&str> = parts.map(|s| s.trim_end_matches(',')).collect();

    Ok(Directive { name, args })
}

/// Parse an instruction line
fn parse_instruction(line: &str) -> Result<Instruction, ParseError> {
    let line = line.trim();

    // Find mnemonic (first word, possibly with condition like "b.lt")
    let mut parts = line.splitn(2, |c: char| c.is_whitespace());

    let mnemonic = parts.next().unwrap_or("");
    let operands_str = parts.next().unwrap_or("");

    // Parse operands (comma-separated, but handle brackets)
    let operands = parse_operands(operands_str);

    Ok(Instruction { mnemonic, operands })
}

/// Parse comma-separated operands, handling brackets for addressing modes
fn parse_operands(s: &str) -> Vec<&str> {
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

#[cfg(test)]
mod tests {
    use super::parse;

    #[test]
    fn test_parse_label() {
        let lines = parse(".Lloop:\n").unwrap();
        assert_eq!(lines[0].label, Some(".Lloop"));
        assert!(lines[0].instruction.is_none());
    }

    #[test]
    fn test_parse_instruction() {
        let lines = parse("    mov x0, #0\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "mov");
        assert_eq!(instr.operands, vec!["x0", "#0"]);
    }

    #[test]
    fn test_parse_directive() {
        let lines = parse(".global _test_loop\n").unwrap();
        let dir = lines[0].directive.as_ref().unwrap();
        assert_eq!(dir.name, "global");
        assert_eq!(dir.args, vec!["_test_loop"]);
    }

    #[test]
    fn test_parse_branch() {
        let lines = parse("    b.lt .Lloop\n").unwrap();
        let instruction = lines[0].instruction.as_ref().unwrap();
        assert!(instruction.is_branch());
        assert_eq!(instruction.get_branch_target(), Some(".Lloop"));
    }

    #[test]
    fn test_parse_label_with_instruction() {
        let lines = parse("_start: mov x0, #1\n").unwrap();
        assert_eq!(lines[0].label, Some("_start"));
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "mov");
    }

    #[test]
    fn test_parse_memory_operand() {
        let lines = parse("    ldr x0, [x1, #8]\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "ldr");
        assert_eq!(instr.operands, vec!["x0", "[x1, #8]"]);
    }

    #[test]
    fn test_indirect_branch_br() {
        let lines = parse("    br x0\n").unwrap();
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
        let lines = parse("    blr x30\n").unwrap();
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
        // Direct unconditional branch
        let lines = parse("    b .Llabel\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch());
        assert!(!instr.is_indirect_branch());
        assert_eq!(instr.get_branch_target(), Some(".Llabel"));

        // Direct branch with link (call)
        let lines = parse("    bl _function\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch());
        assert!(!instr.is_indirect_branch());
        assert_eq!(instr.get_branch_target(), Some("_function"));
    }

    #[test]
    fn test_semicolon_comments() {
        // Semicolon comment at end of line
        let lines = parse("    mov x0, #0 ; initialize counter\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "mov");
        assert_eq!(instr.operands, vec!["x0", "#0"]);

        // Semicolon comment on its own line
        let lines = parse("; this is a comment\n").unwrap();
        assert!(lines[0].instruction.is_none());
        assert!(lines[0].label.is_none());
    }

    #[test]
    fn test_at_sign_comments() {
        // @ comment at end of line (GNU ARM assembler style)
        let lines = parse("    add x0, x0, #1 @ increment\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "add");
        assert_eq!(instr.operands, vec!["x0", "x0", "#1"]);

        // @ comment on its own line
        let lines = parse("@ GNU style comment\n").unwrap();
        assert!(lines[0].instruction.is_none());
    }

    #[test]
    fn test_cpp_style_comments() {
        // // comment at end of line
        let lines = parse("    ret // return to caller\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "ret");
    }

    #[test]
    fn test_c_style_comments() {
        // /* */ comment at end of line
        let lines = parse("    nop /* do nothing */\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "nop");
    }

    #[test]
    fn test_multiple_comment_styles_earliest_wins() {
        // Semicolon appears before //
        let lines = parse("    mov x0, #1 ; comment // not parsed\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.operands, vec!["x0", "#1"]);

        // // appears before ;
        let lines = parse("    mov x0, #2 // comment ; not parsed\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.operands, vec!["x0", "#2"]);
    }

    #[test]
    fn test_is_return() {
        let lines = parse("    ret\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_return());
        assert!(!instr.is_branch());

        // Case insensitivity
        let lines = parse("    RET\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_return());
    }

    #[test]
    fn test_cbz_cbnz_branches() {
        // cbz - compare and branch if zero
        let lines = parse("    cbz x0, .Lzero\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch(), "cbz should be a branch");
        assert!(instr.is_conditional_branch(), "cbz should be conditional");
        assert!(!instr.is_indirect_branch(), "cbz should not be indirect");
        assert_eq!(instr.get_branch_target(), Some(".Lzero"));

        // cbnz - compare and branch if not zero
        let lines = parse("    cbnz w5, .Lnonzero\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch(), "cbnz should be a branch");
        assert!(instr.is_conditional_branch(), "cbnz should be conditional");
        assert_eq!(instr.get_branch_target(), Some(".Lnonzero"));
    }

    #[test]
    fn test_tbz_tbnz_branches() {
        // tbz - test bit and branch if zero (3 operands)
        let lines = parse("    tbz x0, #63, .Lpositive\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch(), "tbz should be a branch");
        assert!(instr.is_conditional_branch(), "tbz should be conditional");
        assert!(!instr.is_indirect_branch(), "tbz should not be indirect");
        assert_eq!(instr.get_branch_target(), Some(".Lpositive"));
        assert_eq!(instr.operands.len(), 3);

        // tbnz - test bit and branch if not zero
        let lines = parse("    tbnz w1, #0, .Lodd\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch(), "tbnz should be a branch");
        assert!(instr.is_conditional_branch(), "tbnz should be conditional");
        assert_eq!(instr.get_branch_target(), Some(".Lodd"));
    }

    #[test]
    fn test_pac_branches() {
        // braaz - branch to register with pointer authentication
        let lines = parse("    braaz x0\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch(), "braaz should be a branch");
        assert!(instr.is_indirect_branch(), "braaz should be indirect");
        assert_eq!(instr.get_branch_target(), None);

        // blraaz - branch with link, pointer authentication
        let lines = parse("    blraaz x1\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch(), "blraaz should be a branch");
        assert!(instr.is_indirect_branch(), "blraaz should be indirect");
    }

    #[test]
    fn test_label_with_directive() {
        let lines = parse("my_data: .quad 0x1234\n").unwrap();
        assert_eq!(lines[0].label, Some("my_data"));
        let dir = lines[0].directive.as_ref().unwrap();
        assert_eq!(dir.name, "quad");
        assert_eq!(dir.args, vec!["0x1234"]);
        assert!(lines[0].instruction.is_none());
    }

    #[test]
    fn test_empty_and_whitespace_lines() {
        // Empty line
        let lines = parse("\n").unwrap();
        assert!(lines[0].label.is_none());
        assert!(lines[0].instruction.is_none());
        assert!(lines[0].directive.is_none());

        // Whitespace only
        let lines = parse("    \t  \n").unwrap();
        assert!(lines[0].label.is_none());
        assert!(lines[0].instruction.is_none());
    }

    #[test]
    fn test_multi_line_parsing() {
        let input = ".global _start
_start:
    mov x0, #0
.Lloop:
    add x0, x0, #1
    cmp x0, #10
    b.lt .Lloop
    ret
";
        let lines = parse(input).unwrap();
        assert_eq!(lines.len(), 8);

        // Check line numbers
        assert_eq!(lines[0].line_number, 1);
        assert_eq!(lines[1].line_number, 2);
        assert_eq!(lines[7].line_number, 8);

        // Check content
        assert!(lines[0].directive.is_some()); // .global
        assert_eq!(lines[1].label, Some("_start"));
        assert_eq!(lines[3].label, Some(".Lloop"));
        assert!(lines[7].instruction.as_ref().unwrap().is_return());
    }

    #[test]
    fn test_original_field_preserves_comments() {
        let input = "    mov x0, #0 ; this is a comment\n";
        let lines = parse(input).unwrap();
        assert_eq!(lines[0].original, "    mov x0, #0 ; this is a comment");
    }

    #[test]
    fn test_post_index_addressing() {
        // Post-indexed: ldr x0, [x1], #8 - comma is outside brackets
        let lines = parse("    ldr x0, [x1], #8\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "ldr");
        assert_eq!(instr.operands, vec!["x0", "[x1]", "#8"]);
    }

    #[test]
    fn test_pre_index_writeback() {
        // Pre-indexed with writeback: ldr x0, [x1, #8]!
        let lines = parse("    ldr x0, [x1, #8]!\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "ldr");
        assert_eq!(instr.operands, vec!["x0", "[x1, #8]!"]);
    }

    #[test]
    fn test_case_insensitivity_branches() {
        // Uppercase
        let lines = parse("    B.LT .Lloop\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch());
        assert!(instr.is_conditional_branch());

        // Mixed case
        let lines = parse("    Cbz x0, .Lzero\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch());
    }

    #[test]
    fn test_non_branch_non_return() {
        let lines = parse("    add x0, x1, x2\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(!instr.is_branch());
        assert!(!instr.is_return());
        assert!(!instr.is_conditional_branch());
        assert!(!instr.is_indirect_branch());
        assert_eq!(instr.get_branch_target(), None);
    }

    #[test]
    fn test_bl_is_unconditional() {
        let lines = parse("    bl _function\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert!(instr.is_branch());
        assert!(
            !instr.is_conditional_branch(),
            "bl is a call, not conditional"
        );
    }

    #[test]
    fn test_instruction_no_operands() {
        let lines = parse("    ret\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "ret");
        assert!(instr.operands.is_empty());

        let lines = parse("    nop\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "nop");
        assert!(instr.operands.is_empty());
    }

    #[test]
    fn test_label_with_dollar_sign() {
        let lines = parse("$Lfoo$bar:\n").unwrap();
        assert_eq!(lines[0].label, Some("$Lfoo$bar"));
    }

    #[test]
    fn test_all_conditional_branch_variants() {
        let conditions = [
            "b.eq", "b.ne", "b.cs", "b.cc", "b.mi", "b.pl", "b.vs", "b.vc", "b.hi", "b.ls", "b.ge",
            "b.lt", "b.gt", "b.le", "b.al",
        ];

        for cond in conditions {
            let input = format!("    {} .Ltarget\n", cond);
            let lines = parse(&input).unwrap();
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
        // Load pair
        let lines = parse("    ldp x0, x1, [sp, #16]\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "ldp");
        assert_eq!(instr.operands, vec!["x0", "x1", "[sp, #16]"]);

        // Store pair
        let lines = parse("    stp x29, x30, [sp, #-16]!\n").unwrap();
        let instr = lines[0].instruction.as_ref().unwrap();
        assert_eq!(instr.mnemonic, "stp");
        assert_eq!(instr.operands, vec!["x29", "x30", "[sp, #-16]!"]);
    }
}
