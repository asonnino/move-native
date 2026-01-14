//! Control Flow Graph builder for Arm64 assembly
//!
//! Builds a CFG from parsed assembly and identifies back-edges for gas instrumentation.

use std::collections::HashMap;

use crate::parser::ParsedLine;

/// A basic block in the control flow graph
#[derive(Debug, Clone)]
pub struct BasicBlock {
    /// Unique identifier for this block
    pub id: usize,
    /// Label at the start of this block (if any)
    pub label: Option<String>,
    /// Indices into the original parsed lines
    pub line_indices: Vec<usize>,
    /// IDs of successor blocks
    pub successors: Vec<usize>,
    /// Whether the terminating branch is a back-edge
    pub has_back_edge: bool,
    /// Target label of the back-edge (if has_back_edge is true)
    pub back_edge_target: Option<String>,
}

/// Control flow graph
#[derive(Debug)]
pub struct Cfg {
    /// All basic blocks
    pub blocks: Vec<BasicBlock>,
    /// Map from label name to block ID
    pub label_to_block: HashMap<String, usize>,
}

impl Cfg {
    /// Get a block by ID
    pub fn get_block(&self, id: usize) -> Option<&BasicBlock> {
        self.blocks.get(id)
    }

    /// Check if a branch from `from_block` to `target_label` is a back-edge
    pub fn is_back_edge(&self, from_block: usize, target_label: &str) -> bool {
        if let Some(&target_block) = self.label_to_block.get(target_label) {
            // Back-edge if target block ID <= source block ID
            target_block <= from_block
        } else {
            false
        }
    }
}

/// Build a CFG from parsed assembly lines
pub fn build(lines: &[ParsedLine]) -> Cfg {
    // First pass: identify all labels and their positions
    let mut label_positions: HashMap<String, usize> = HashMap::new();
    for (idx, line) in lines.iter().enumerate() {
        if let Some(ref label) = line.label {
            label_positions.insert(label.clone(), idx);
        }
    }

    // Second pass: identify basic block boundaries
    // A new block starts at:
    // - The beginning of the file
    // - Any label
    // - The instruction after a branch
    let mut block_starts: Vec<usize> = Vec::new();
    let mut prev_was_branch = false;

    for (idx, line) in lines.iter().enumerate() {
        let is_start = idx == 0 || line.label.is_some() || prev_was_branch;

        if is_start && has_code(line, lines, idx) {
            if block_starts.last() != Some(&idx) {
                block_starts.push(idx);
            }
        }

        prev_was_branch = line
            .instruction
            .as_ref()
            .map(|i| i.is_branch() || i.is_return())
            .unwrap_or(false);
    }

    // Third pass: create basic blocks
    let mut blocks: Vec<BasicBlock> = Vec::new();
    let mut label_to_block: HashMap<String, usize> = HashMap::new();

    for (block_idx, &start_idx) in block_starts.iter().enumerate() {
        let end_idx = block_starts
            .get(block_idx + 1)
            .copied()
            .unwrap_or(lines.len());

        // Collect line indices for this block
        let line_indices: Vec<usize> = (start_idx..end_idx).collect();

        // Find the label for this block (if any)
        let label = lines[start_idx].label.clone();

        // Register this block for any labels it contains
        for &idx in &line_indices {
            if let Some(ref lbl) = lines[idx].label {
                label_to_block.insert(lbl.clone(), block_idx);
            }
        }

        blocks.push(BasicBlock {
            id: block_idx,
            label,
            line_indices,
            successors: Vec::new(),
            has_back_edge: false,
            back_edge_target: None,
        });
    }

    // Fourth pass: compute successors and identify back-edges
    for block_idx in 0..blocks.len() {
        let block = &blocks[block_idx];
        let mut successors = Vec::new();
        let mut has_back_edge = false;
        let mut back_edge_target = None;

        // Find the terminating instruction
        let term_instr = block
            .line_indices
            .iter()
            .rev()
            .find_map(|&idx| lines[idx].instruction.as_ref());

        if let Some(instr) = term_instr {
            if instr.is_branch() {
                if let Some(target) = instr.get_branch_target() {
                    if let Some(&target_block) = label_to_block.get(target) {
                        successors.push(target_block);

                        // Check if this is a back-edge
                        if target_block <= block_idx {
                            has_back_edge = true;
                            back_edge_target = Some(target.to_string());
                        }
                    }

                    // Conditional branches also fall through
                    if instr.is_conditional_branch() && block_idx + 1 < blocks.len() {
                        successors.push(block_idx + 1);
                    }
                }
            } else if !instr.is_return() {
                // Non-branch, non-return falls through
                if block_idx + 1 < blocks.len() {
                    successors.push(block_idx + 1);
                }
            }
        } else {
            // No terminating instruction, fall through
            if block_idx + 1 < blocks.len() {
                successors.push(block_idx + 1);
            }
        }

        // Update the block
        let block = &mut blocks[block_idx];
        block.successors = successors;
        block.has_back_edge = has_back_edge;
        block.back_edge_target = back_edge_target;
    }

    Cfg {
        blocks,
        label_to_block,
    }
}

/// Check if there's any code at or after this position in the same logical block
fn has_code(line: &ParsedLine, lines: &[ParsedLine], idx: usize) -> bool {
    // Check current line
    if line.instruction.is_some() {
        return true;
    }

    // Look ahead for code before the next label
    for future_line in lines.iter().skip(idx + 1) {
        if future_line.label.is_some() {
            break;
        }
        if future_line.instruction.is_some() {
            return true;
        }
    }

    false
}

/// Count the number of actual instructions in a block (excluding directives, labels, empty lines)
pub fn count_instructions(block: &BasicBlock, lines: &[ParsedLine]) -> usize {
    block
        .line_indices
        .iter()
        .filter(|&&idx| lines[idx].instruction.is_some())
        .count()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    #[test]
    fn test_simple_loop() {
        let input = r#"
_test_loop:
    mov x0, #0
    mov x1, #1000000

.Lloop:
    add x0, x0, #1
    cmp x0, x1
    b.lt .Lloop

    ret
"#;
        let parser = Parser {};
        let lines = parser.parse(input).unwrap();
        let cfg = build(&lines);

        // Should have multiple blocks
        assert!(cfg.blocks.len() >= 2);

        // Find the block with the back-edge
        let back_edge_block = cfg.blocks.iter().find(|b| b.has_back_edge);
        assert!(back_edge_block.is_some());

        let block = back_edge_block.unwrap();
        assert_eq!(block.back_edge_target, Some(".Lloop".to_string()));
    }

    #[test]
    fn test_label_mapping() {
        let input = r#"
.Lstart:
    mov x0, #0
.Lloop:
    add x0, x0, #1
    b .Lloop
"#;
        let parser = Parser {};
        let lines = parser.parse(input).unwrap();
        let cfg = build(&lines);

        assert!(cfg.label_to_block.contains_key(".Lstart"));
        assert!(cfg.label_to_block.contains_key(".Lloop"));
    }
}
