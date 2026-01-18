//! Generic CFG builder
//!
//! Builds a control flow graph from a sequence of instructions implementing
//! the [`InstructionInfo`] trait.

use std::collections::{HashMap, HashSet};

use petgraph::{algo::dominators, graph::DiGraph};

use crate::{
    graph::{BlockData, Cfg},
    InstructionInfo,
};

/// Build a CFG from a sequence of instructions.
///
/// The instructions must implement [`InstructionInfo`] to provide the
/// control flow information needed for CFG construction.
pub fn build_cfg<I: InstructionInfo>(instructions: &[I]) -> Cfg {
    CfgBuilder::new(instructions).build()
}

/// Builder for constructing a CFG from instructions
struct CfgBuilder<'a, I: InstructionInfo> {
    instructions: &'a [I],
    graph: DiGraph<BlockData, ()>,
    target_to_block: HashMap<usize, petgraph::graph::NodeIndex>,
    nodes: Vec<petgraph::graph::NodeIndex>,
}

impl<'a, I: InstructionInfo> CfgBuilder<'a, I> {
    fn new(instructions: &'a [I]) -> Self {
        Self {
            instructions,
            graph: DiGraph::new(),
            target_to_block: HashMap::new(),
            nodes: Vec::new(),
        }
    }

    fn build(mut self) -> Cfg {
        let block_starts = self.find_block_boundaries();
        self.create_blocks(&block_starts);
        self.add_edges();
        self.identify_back_edges();

        Cfg::new(self.graph, self.target_to_block)
    }

    /// Find basic block boundaries.
    ///
    /// A new block starts at:
    /// - The beginning of the code
    /// - Any branch target
    /// - The instruction after a branch
    fn find_block_boundaries(&self) -> Vec<usize> {
        // Collect all branch targets first
        let branch_targets: HashSet<usize> = self
            .instructions
            .iter()
            .filter_map(|i| i.branch_target())
            .collect();

        let mut block_starts = Vec::new();
        let mut previous_was_branch = false;

        for (idx, item) in self.instructions.iter().enumerate() {
            // Check if this instruction is a branch target
            let is_branch_target = branch_targets.contains(&item.as_target());

            let is_start = idx == 0 || is_branch_target || previous_was_branch;

            if is_start {
                block_starts.push(idx);
            }

            previous_was_branch = item.is_branch() || item.is_return();
        }

        block_starts
    }

    /// Create graph nodes for each basic block.
    fn create_blocks(&mut self, block_starts: &[usize]) {
        for (block_idx, &start_idx) in block_starts.iter().enumerate() {
            let end_idx = block_starts
                .get(block_idx + 1)
                .copied()
                .unwrap_or(self.instructions.len());

            let instruction_range = start_idx..end_idx;

            // Get the target identifier from the first item in the block
            let label = Some(self.instructions[start_idx].as_target());

            // All items are instructions, count = range length
            let instruction_count = instruction_range.len();

            let node = self.graph.add_node(BlockData {
                label,
                instruction_range: instruction_range.clone(),
                back_edge_target: None,
                terminator_index: None,
                instruction_count,
            });
            self.nodes.push(node);

            // Register all targets in this block
            for idx in instruction_range {
                let target = self.instructions[idx].as_target();
                self.target_to_block.insert(target, node);
            }
        }
    }

    /// Add edges based on control flow and record terminator indices.
    fn add_edges(&mut self) {
        for (block_idx, &node) in self.nodes.iter().enumerate() {
            let block = &self.graph[node];

            // The terminator is the last instruction in the block
            // (all items are instructions, so last in range)
            if let Some(terminator_idx) = block.instruction_range.clone().last() {
                let item = &self.instructions[terminator_idx];

                if item.is_branch() || item.is_return() {
                    self.graph[node].terminator_index = Some(terminator_idx);
                }

                // Add edge to branch target (if direct branch, not a call)
                if item.is_branch() && !item.is_call() {
                    if let Some(target) = item.branch_target() {
                        if let Some(&target_node) = self.target_to_block.get(&target) {
                            self.graph.add_edge(node, target_node, ());
                        }
                    }
                }

                // Add fall-through edge (if not return and not unconditional jump)
                if !item.is_return() && !item.is_unconditional_jump() {
                    if let Some(&next_node) = self.nodes.get(block_idx + 1) {
                        self.graph.add_edge(node, next_node, ());
                    }
                }
            } else if let Some(&next_node) = self.nodes.get(block_idx + 1) {
                // Empty block - fall through to next block
                self.graph.add_edge(node, next_node, ());
            }
        }
    }

    /// Compute dominators and mark back-edges.
    ///
    /// A back-edge is an edge A → B where B dominates A.
    fn identify_back_edges(&mut self) {
        if self.nodes.is_empty() {
            return;
        }

        let entry = self.nodes[0];
        let dominators = dominators::simple_fast(&self.graph, entry);

        let back_edges: Vec<_> = self
            .nodes
            .iter()
            .filter_map(|&node| {
                self.graph
                    .neighbors(node)
                    .find(|&successor| {
                        dominators
                            .dominators(node)
                            .is_some_and(|mut iter| iter.any(|d| d == successor))
                    })
                    .map(|target| (node, target))
            })
            .collect();

        for (node, _target_node) in back_edges {
            debug_assert!(
                self.graph[node].instruction_count > 0,
                "back-edge should have instructions"
            );
            // Get branch target directly from the terminator instruction
            if let Some(term_idx) = self.graph[node].terminator_index {
                if let Some(target) = self.instructions[term_idx].branch_target() {
                    self.graph[node].back_edge_target = Some(target);
                }
            }
        }
    }
}
