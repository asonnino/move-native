//! Control Flow Graph builder for Arm64 assembly
//!
//! Builds a CFG from parsed assembly and identifies back-edges for gas instrumentation.
//! Uses petgraph as the primary graph representation.

use std::collections::HashMap;

use petgraph::algo::dominators::simple_fast;
use petgraph::graph::{DiGraph, NodeIndex};

use crate::parser::ParsedLine;

/// Data stored in each basic block node
#[derive(Debug, Clone)]
pub struct BlockData {
    /// Label at the start of this block (if any)
    pub label: Option<String>,
    /// Indices into the original parsed lines
    pub line_indices: Vec<usize>,
    /// Whether the terminating branch is a back-edge
    pub has_back_edge: bool,
    /// Target label of the back-edge (if has_back_edge is true)
    pub back_edge_target: Option<String>,
}

/// Control flow graph backed by petgraph
#[derive(Debug)]
pub struct Cfg {
    /// The underlying directed graph
    graph: DiGraph<BlockData, ()>,
    /// Map from label name to block node
    label_to_block: HashMap<String, NodeIndex>,
}

impl Cfg {
    /// Iterate over all block indices
    pub fn blocks(&self) -> impl Iterator<Item = NodeIndex> + '_ {
        self.graph.node_indices()
    }

    /// Get the number of blocks
    pub fn block_count(&self) -> usize {
        self.graph.node_count()
    }

    /// Get block data by node index
    pub fn block(&self, idx: NodeIndex) -> &BlockData {
        &self.graph[idx]
    }

    /// Get successors of a block
    pub fn successors(&self, idx: NodeIndex) -> impl Iterator<Item = NodeIndex> + '_ {
        self.graph.neighbors(idx)
    }

    /// Get block by label
    pub fn block_by_label(&self, label: &str) -> Option<NodeIndex> {
        self.label_to_block.get(label).copied()
    }

    /// Check if a label exists in the CFG
    pub fn has_label(&self, label: &str) -> bool {
        self.label_to_block.contains_key(label)
    }

    /// Check if a branch from `from_block` to `target_label` is a back-edge
    /// Uses cached back-edge information computed via dominator analysis
    pub fn is_back_edge(&self, from_block: NodeIndex, target_label: &str) -> bool {
        let block = &self.graph[from_block];
        block.has_back_edge && block.back_edge_target.as_deref() == Some(target_label)
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

    // Third pass: create graph nodes for basic blocks
    let mut graph: DiGraph<BlockData, ()> = DiGraph::new();
    let mut label_to_block: HashMap<String, NodeIndex> = HashMap::new();
    let mut nodes: Vec<NodeIndex> = Vec::new();

    for (block_idx, &start_idx) in block_starts.iter().enumerate() {
        let end_idx = block_starts
            .get(block_idx + 1)
            .copied()
            .unwrap_or(lines.len());

        // Collect line indices for this block
        let line_indices: Vec<usize> = (start_idx..end_idx).collect();

        // Find the label for this block (if any)
        let label = lines[start_idx].label.clone();

        // Create the node
        let node = graph.add_node(BlockData {
            label,
            line_indices: line_indices.clone(),
            has_back_edge: false,
            back_edge_target: None,
        });
        nodes.push(node);

        // Register this block for any labels it contains
        for &idx in &line_indices {
            if let Some(ref lbl) = lines[idx].label {
                label_to_block.insert(lbl.clone(), node);
            }
        }
    }

    // Fourth pass: add edges based on control flow
    for (block_idx, &node) in nodes.iter().enumerate() {
        let block = &graph[node];

        // Find the terminating instruction
        let term_instr = block
            .line_indices
            .iter()
            .rev()
            .find_map(|&idx| lines[idx].instruction.as_ref());

        if let Some(instr) = term_instr {
            if instr.is_branch() {
                if let Some(target) = instr.get_branch_target() {
                    if let Some(&target_node) = label_to_block.get(target) {
                        graph.add_edge(node, target_node, ());
                    }

                    // Conditional branches also fall through
                    if instr.is_conditional_branch() && block_idx + 1 < nodes.len() {
                        graph.add_edge(node, nodes[block_idx + 1], ());
                    }
                }
            } else if !instr.is_return() {
                // Non-branch, non-return falls through
                if block_idx + 1 < nodes.len() {
                    graph.add_edge(node, nodes[block_idx + 1], ());
                }
            }
        } else {
            // No terminating instruction, fall through
            if block_idx + 1 < nodes.len() {
                graph.add_edge(node, nodes[block_idx + 1], ());
            }
        }
    }

    // Fifth pass: compute dominators and identify back-edges
    // A back-edge is an edge A → B where B dominates A
    if !nodes.is_empty() {
        let entry = nodes[0];
        let dominators = simple_fast(&graph, entry);

        // Collect back-edge information
        let mut back_edge_info: Vec<(NodeIndex, Option<String>)> = Vec::new();

        for &node in &nodes {
            for succ in graph.neighbors(node) {
                // Check if successor dominates this block
                let succ_dominates_block = dominators
                    .dominators(node)
                    .map(|mut iter| iter.any(|dom| dom == succ))
                    .unwrap_or(false);

                if succ_dominates_block {
                    // Find the target label from the successor block
                    let succ_block = &graph[succ];
                    let target_label = if let Some(ref label) = succ_block.label {
                        Some(label.clone())
                    } else {
                        // Look for any label in the target block's line indices
                        succ_block
                            .line_indices
                            .iter()
                            .find_map(|&line_idx| lines[line_idx].label.clone())
                    };
                    back_edge_info.push((node, target_label));
                    break; // Only need to mark one back-edge per block
                }
            }
        }

        // Apply back-edge information
        for (node, target_label) in back_edge_info {
            let block = &mut graph[node];
            block.has_back_edge = true;
            block.back_edge_target = target_label;
        }
    }

    Cfg {
        graph,
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
pub fn count_instructions(cfg: &Cfg, block: NodeIndex, lines: &[ParsedLine]) -> usize {
    cfg.block(block)
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
        assert!(cfg.block_count() >= 2);

        // Find the block with the back-edge
        let back_edge_block = cfg.blocks().find(|&b| cfg.block(b).has_back_edge);
        assert!(back_edge_block.is_some());

        let block = cfg.block(back_edge_block.unwrap());
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

        assert!(cfg.has_label(".Lstart"));
        assert!(cfg.has_label(".Lloop"));
    }

    #[test]
    fn test_nested_loops() {
        // Outer loop with inner loop - both should have back-edges
        let input = r#"
_nested:
    mov x0, #0
.Louter:
    mov x1, #0
.Linner:
    add x1, x1, #1
    cmp x1, #10
    b.lt .Linner
    add x0, x0, #1
    cmp x0, #10
    b.lt .Louter
    ret
"#;
        let parser = Parser {};
        let lines = parser.parse(input).unwrap();
        let cfg = build(&lines);

        // Should have exactly 2 back-edges
        let back_edge_count = cfg.blocks().filter(|&b| cfg.block(b).has_back_edge).count();
        assert_eq!(back_edge_count, 2, "Expected 2 back-edges for nested loops");

        // Verify targets
        let inner_be = cfg
            .blocks()
            .find(|&b| cfg.block(b).back_edge_target == Some(".Linner".to_string()));
        let outer_be = cfg
            .blocks()
            .find(|&b| cfg.block(b).back_edge_target == Some(".Louter".to_string()));
        assert!(inner_be.is_some(), "Should have back-edge to .Linner");
        assert!(outer_be.is_some(), "Should have back-edge to .Louter");
    }

    #[test]
    fn test_diamond_no_back_edge() {
        // Diamond pattern: entry -> then/else -> end
        // No back-edges should be detected (all forward branches)
        let input = r#"
_diamond:
    cmp x0, #0
    b.eq .Lthen
    mov x1, #1
    b .Lend
.Lthen:
    mov x1, #2
.Lend:
    ret
"#;
        let parser = Parser {};
        let lines = parser.parse(input).unwrap();
        let cfg = build(&lines);

        // No back-edges in a diamond pattern
        let back_edge_count = cfg.blocks().filter(|&b| cfg.block(b).has_back_edge).count();
        assert_eq!(back_edge_count, 0, "Diamond pattern should have no back-edges");
    }

    #[test]
    fn test_self_loop() {
        // Degenerate case: block branches to itself
        let input = r#"
_spin:
.Lspin:
    b .Lspin
"#;
        let parser = Parser {};
        let lines = parser.parse(input).unwrap();
        let cfg = build(&lines);

        let back_edge_block = cfg.blocks().find(|&b| cfg.block(b).has_back_edge);
        assert!(back_edge_block.is_some(), "Should detect self-loop back-edge");
        assert_eq!(
            cfg.block(back_edge_block.unwrap()).back_edge_target,
            Some(".Lspin".to_string())
        );
    }

    #[test]
    fn test_do_while_loop() {
        // Do-while style: body executes at least once, check at end
        let input = r#"
_do_while:
.Lbody:
    add x0, x0, #1
    cmp x0, #100
    b.lt .Lbody
    ret
"#;
        let parser = Parser {};
        let lines = parser.parse(input).unwrap();
        let cfg = build(&lines);

        let back_edge_block = cfg.blocks().find(|&b| cfg.block(b).has_back_edge);
        assert!(back_edge_block.is_some(), "Should detect do-while back-edge");
        assert_eq!(
            cfg.block(back_edge_block.unwrap()).back_edge_target,
            Some(".Lbody".to_string())
        );
    }

    #[test]
    fn test_multiple_independent_loops() {
        // Two separate loops in sequence
        let input = r#"
_two_loops:
    mov x0, #0
.Lloop1:
    add x0, x0, #1
    cmp x0, #10
    b.lt .Lloop1

    mov x1, #0
.Lloop2:
    add x1, x1, #1
    cmp x1, #10
    b.lt .Lloop2
    ret
"#;
        let parser = Parser {};
        let lines = parser.parse(input).unwrap();
        let cfg = build(&lines);

        // Should have exactly 2 back-edges
        let back_edge_count = cfg.blocks().filter(|&b| cfg.block(b).has_back_edge).count();
        assert_eq!(
            back_edge_count, 2,
            "Expected 2 back-edges for two independent loops"
        );

        let loop1_be = cfg
            .blocks()
            .find(|&b| cfg.block(b).back_edge_target == Some(".Lloop1".to_string()));
        let loop2_be = cfg
            .blocks()
            .find(|&b| cfg.block(b).back_edge_target == Some(".Lloop2".to_string()));
        assert!(loop1_be.is_some(), "Should have back-edge to .Lloop1");
        assert!(loop2_be.is_some(), "Should have back-edge to .Lloop2");
    }

    #[test]
    fn test_is_back_edge_method() {
        let input = r#"
_test:
    mov x0, #0
.Lloop:
    add x0, x0, #1
    b.lt .Lloop
    ret
"#;
        let parser = Parser {};
        let lines = parser.parse(input).unwrap();
        let cfg = build(&lines);

        // Find the block that has the back-edge
        let back_edge_node = cfg.blocks().find(|&b| cfg.block(b).has_back_edge).unwrap();

        // is_back_edge should return true for the correct block/target
        assert!(cfg.is_back_edge(back_edge_node, ".Lloop"));

        // is_back_edge should return false for other targets
        assert!(!cfg.is_back_edge(back_edge_node, ".Lnonexistent"));
    }

    #[test]
    fn test_successors() {
        let input = r#"
_test:
    cmp x0, #0
    b.eq .Lthen
    mov x1, #1
    b .Lend
.Lthen:
    mov x1, #2
.Lend:
    ret
"#;
        let parser = Parser {};
        let lines = parser.parse(input).unwrap();
        let cfg = build(&lines);

        // Entry block should have 2 successors (conditional branch + fall-through)
        let entry = cfg.blocks().next().unwrap();
        let succ_count = cfg.successors(entry).count();
        assert_eq!(succ_count, 2, "Entry block should have 2 successors");
    }
}