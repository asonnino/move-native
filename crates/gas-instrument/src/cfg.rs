//! Control Flow Graph builder for Arm64 assembly
//!
//! Builds a CFG from parsed assembly and identifies back-edges for gas instrumentation.
//! Uses petgraph as the primary graph representation.
//!
//! ## Back-Edge Detection
//!
//! Back-edges are identified using dominator analysis: an edge A → B is a back-edge
//! if B dominates A. This is the standard definition used in compiler theory.
//!
//! ## Unreachable Code
//!
//! Dominator analysis only works for code reachable from the entry point. Loops in
//! unreachable code will NOT be detected as back-edges and will NOT receive gas checks.
//! This is by design: the `native-verifier` crate is responsible for rejecting modules
//! that contain unreachable code.

use std::{collections::HashMap, ops::Range};

use petgraph::{
    algo::dominators::{self},
    graph::{DiGraph, NodeIndex},
};

use crate::parser::ParsedLine;

/// Data stored in each basic block node
#[derive(Debug, Clone)]
pub struct BlockData {
    /// Label at the start of this block (if any)
    pub label: Option<String>,

    /// Range of indices into the original parsed lines.
    /// E.g., for a block containing lines 3, 4, 5 this would be `3..6`
    pub line_indices: Range<usize>,

    /// Target label of the back-edge, if this block ends with one.
    /// E.g., `Some(".Lloop")` for a block ending with `b.lt .Lloop` that loops back
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
        self.graph[from_block].back_edge_target.as_deref() == Some(target_label)
    }

    /// Build a CFG from parsed assembly lines
    pub fn from_lines(lines: &[ParsedLine]) -> Self {
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
        let mut previous_was_branch = false;

        for (idx, line) in lines.iter().enumerate() {
            let is_start = idx == 0 || line.label.is_some() || previous_was_branch;

            if is_start && Self::has_code(line, lines, idx) {
                block_starts.push(idx);
            }

            previous_was_branch = line
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

            // Line indices for this block
            let line_indices = start_idx..end_idx;

            // Find the label for this block (if any)
            let label = lines[start_idx].label.clone();

            // Create the node
            let node = graph.add_node(BlockData {
                label,
                line_indices: line_indices.clone(),
                back_edge_target: None,
            });
            nodes.push(node);

            // Register this block for any labels it contains
            for idx in line_indices {
                if let Some(ref lbl) = lines[idx].label {
                    label_to_block.insert(lbl.clone(), node);
                }
            }
        }

        // Fourth pass: add edges based on control flow
        for (block_idx, &node) in nodes.iter().enumerate() {
            let block = &graph[node];

            // Find the terminating instruction
            let terminating_instruction = block
                .line_indices
                .clone()
                .rev()
                .find_map(|idx| lines[idx].instruction.as_ref());

            if let Some(instruction) = terminating_instruction {
                // Add edge to branch target (but not for calls - they return to next instruction)
                if instruction.is_branch() && !instruction.is_call() {
                    if let Some(target) = instruction.get_branch_target() {
                        if let Some(&target_node) = label_to_block.get(target) {
                            graph.add_edge(node, target_node, ());
                        }
                    }
                }

                // Fall through unless it's a return or unconditional jump
                if !instruction.is_return() && !instruction.is_unconditional_jump() {
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
        if nodes.is_empty() {
            return Self {
                graph,
                label_to_block,
            };
        }

        // Compute dominator tree: B dominates A if every path from entry to A goes through B
        let entry = nodes[0];
        let dominators = dominators::simple_fast(&graph, entry);

        // Collect back-edge information
        let mut back_edge_info: Vec<(NodeIndex, Option<String>)> = Vec::new();
        for &node in &nodes {
            for successor in graph.neighbors(node) {
                // Check if successor dominates this block
                let successor_dominates_block = dominators
                    .dominators(node)
                    .map(|mut iter| iter.any(|d| d == successor))
                    .unwrap_or(false);

                if successor_dominates_block {
                    // Find the target label from the successor block.
                    // Note: target_label may be None for malformed input. We don't panic
                    // here because this processes untrusted input. The verifier will
                    // reject any uninstrumented back-edges later.
                    let target_label = graph[successor].label.clone();
                    back_edge_info.push((node, target_label));
                    break; // Only need to mark one back-edge per block
                }
            }
        }

        // Apply back-edge information
        for (node, target_label) in back_edge_info {
            graph[node].back_edge_target = target_label;
        }

        Self {
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
    pub fn count_instructions(&self, block: NodeIndex, lines: &[ParsedLine]) -> usize {
        self.block(block)
            .line_indices
            .clone()
            .filter(|&idx| lines[idx].instruction.is_some())
            .count()
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;

    use crate::{parser::ParsedLine, parser::Parser, Cfg};

    /// Helper to reduce test boilerplate: parses assembly and builds CFG
    fn build_cfg(input: &str) -> (Cfg, Vec<ParsedLine>) {
        let parser = Parser {};
        let lines = parser.parse(input).unwrap();
        let cfg = Cfg::from_lines(&lines);
        (cfg, lines)
    }

    #[test]
    fn test_simple_loop() {
        let (cfg, _) = build_cfg(indoc! {"
            _test_loop:
                mov x0, #0
                mov x1, #1000000
            .Lloop:
                add x0, x0, #1
                cmp x0, x1
                b.lt .Lloop
                ret
        "});

        assert!(cfg.block_count() >= 2);

        let back_edge_block = cfg
            .blocks()
            .find(|&b| cfg.block(b).back_edge_target.is_some());
        assert!(back_edge_block.is_some());

        let block = cfg.block(back_edge_block.unwrap());
        assert_eq!(block.back_edge_target, Some(".Lloop".to_string()));
    }

    #[test]
    fn test_label_mapping() {
        let (cfg, _) = build_cfg(indoc! {"
            .Lstart:
                mov x0, #0
            .Lloop:
                add x0, x0, #1
                b .Lloop
        "});

        assert!(cfg.has_label(".Lstart"));
        assert!(cfg.has_label(".Lloop"));
    }

    #[test]
    fn test_nested_loops() {
        let (cfg, _) = build_cfg(indoc! {"
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
        "});

        let back_edge_count = cfg
            .blocks()
            .filter(|&b| cfg.block(b).back_edge_target.is_some())
            .count();
        assert_eq!(back_edge_count, 2, "Expected 2 back-edges for nested loops");

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
        let (cfg, _) = build_cfg(indoc! {"
            _diamond:
                cmp x0, #0
                b.eq .Lthen
                mov x1, #1
                b .Lend
            .Lthen:
                mov x1, #2
            .Lend:
                ret
        "});

        let back_edge_count = cfg
            .blocks()
            .filter(|&b| cfg.block(b).back_edge_target.is_some())
            .count();
        assert_eq!(
            back_edge_count, 0,
            "Diamond pattern should have no back-edges"
        );
    }

    #[test]
    fn test_self_loop() {
        let (cfg, _) = build_cfg(indoc! {"
            _spin:
            .Lspin:
                b .Lspin
        "});

        let back_edge_block = cfg
            .blocks()
            .find(|&b| cfg.block(b).back_edge_target.is_some());
        assert!(
            back_edge_block.is_some(),
            "Should detect self-loop back-edge"
        );
        assert_eq!(
            cfg.block(back_edge_block.unwrap()).back_edge_target,
            Some(".Lspin".to_string())
        );
    }

    #[test]
    fn test_do_while_loop() {
        let (cfg, _) = build_cfg(indoc! {"
            _do_while:
            .Lbody:
                add x0, x0, #1
                cmp x0, #100
                b.lt .Lbody
                ret
        "});

        let back_edge_block = cfg
            .blocks()
            .find(|&b| cfg.block(b).back_edge_target.is_some());
        assert!(
            back_edge_block.is_some(),
            "Should detect do-while back-edge"
        );
        assert_eq!(
            cfg.block(back_edge_block.unwrap()).back_edge_target,
            Some(".Lbody".to_string())
        );
    }

    #[test]
    fn test_multiple_independent_loops() {
        let (cfg, _) = build_cfg(indoc! {"
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
        "});

        let back_edge_count = cfg
            .blocks()
            .filter(|&b| cfg.block(b).back_edge_target.is_some())
            .count();
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
        let (cfg, _) = build_cfg(indoc! {"
            _test:
                mov x0, #0
            .Lloop:
                add x0, x0, #1
                b.lt .Lloop
                ret
        "});

        let back_edge_node = cfg
            .blocks()
            .find(|&b| cfg.block(b).back_edge_target.is_some())
            .unwrap();

        assert!(cfg.is_back_edge(back_edge_node, ".Lloop"));
        assert!(!cfg.is_back_edge(back_edge_node, ".Lnonexistent"));
    }

    #[test]
    fn test_successors() {
        let (cfg, _) = build_cfg(indoc! {"
            _test:
                cmp x0, #0
                b.eq .Lthen
                mov x1, #1
                b .Lend
            .Lthen:
                mov x1, #2
            .Lend:
                ret
        "});

        let entry = cfg.blocks().next().unwrap();
        let successor_count = cfg.successors(entry).count();
        assert_eq!(successor_count, 2, "Entry block should have 2 successors");
    }

    #[test]
    fn test_call_falls_through() {
        let (cfg, lines) = build_cfg(indoc! {"
            _caller:
                mov x0, #1
                bl _callee
                add x0, x0, #1
                ret
            _callee:
                ret
        "});

        let caller_block = cfg.blocks().find(|&b| {
            let block = cfg.block(b);
            block.line_indices.clone().any(|idx| {
                lines[idx]
                    .instruction
                    .as_ref()
                    .map(|i| i.mnemonic == "bl")
                    .unwrap_or(false)
            })
        });
        assert!(caller_block.is_some(), "Should find block with bl");

        let successor_count = cfg.successors(caller_block.unwrap()).count();
        assert_eq!(
            successor_count, 1,
            "bl should only fall through, not branch to callee"
        );

        let back_edge_count = cfg
            .blocks()
            .filter(|&b| cfg.block(b).back_edge_target.is_some())
            .count();
        assert_eq!(back_edge_count, 0, "Calls should not create back-edges");
    }

    #[test]
    fn test_recursive_call_no_back_edge() {
        let (cfg, _) = build_cfg(indoc! {"
            _factorial:
                cmp x0, #1
                b.le .Lbase
                sub x0, x0, #1
                bl _factorial
                mul x0, x0, x1
                ret
            .Lbase:
                mov x0, #1
                ret
        "});

        let back_edge_count = cfg
            .blocks()
            .filter(|&b| cfg.block(b).back_edge_target.is_some())
            .count();
        assert_eq!(
            back_edge_count, 0,
            "Recursive call should not create a back-edge"
        );
    }
}
