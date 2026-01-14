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

        // Unconditional branches
        if mnemonic == "b" || mnemonic == "bl" {
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
    pub fn get_branch_target(&self) -> Option<&str> {
        if !self.is_branch() {
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

    /// Remove C-style and C++-style comments from a line
    fn remove_comments<'a>(&self, line: &'a str) -> &'a str {
        // Handle // comments
        if let Some(pos) = line.find("//") {
            return &line[..pos];
        }
        // Handle /* */ comments (simplified - assumes single line)
        if let Some(start) = line.find("/*") {
            if let Some(_end) = line.find("*/") {
                // For simplicity, just return up to the comment start
                return &line[..start];
            }
        }
        line
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
}
