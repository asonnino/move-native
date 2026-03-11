// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! CFG data structures

use std::collections::VecDeque;
use std::{
    collections::{HashMap, HashSet},
    ops::Range,
};

pub type BlockIndex = petgraph::graph::NodeIndex;

pub(crate) type InnerBlockGraph = petgraph::graph::DiGraph<BlockData, ()>;

/// Data stored in each basic block node
#[derive(Debug)]
pub struct BlockData {
    /// Range of indices into the original instruction list.
    /// E.g., for a block containing instructions 3, 4, 5 this would be `3..6`
    pub instruction_range: Range<usize>,

    /// Branch target of the back-edge, if this block ends with one.
    pub back_edge_target: Option<usize>,

    /// Whether this block ends with an explicit terminator instruction.
    ///
    /// A **terminator** is the instruction that ends a basic block's control flow -
    /// either a branch instruction (conditional or unconditional) or a return.
    /// Blocks without an explicit terminator "fall through" to the next block.
    pub has_explicit_terminator: bool,

    /// Number of actual instructions in this block
    pub instruction_count: usize,

    /// Targets of call instructions (`bl`) in this block.
    /// Values are instruction indices (text) or byte offsets (binary),
    /// matching the `CfgInstruction::branch_target()` convention.
    pub call_targets: Vec<usize>,
}

/// Block-level control flow graph backed by petgraph.
///
/// Contains basic blocks, edges (branches/fall-through), and back-edge info.
pub struct BlockGraph {
    /// The underlying directed graph
    graph: InnerBlockGraph,
    /// Maps instruction/byte targets to the block containing them.
    /// Used to resolve call targets (`bl`) to blocks during reachability analysis.
    target_to_block: HashMap<usize, BlockIndex>,
}

impl BlockGraph {
    /// Create a new block-level CFG (used by builder).
    pub(crate) fn new(graph: InnerBlockGraph, target_to_block: HashMap<usize, BlockIndex>) -> Self {
        Self {
            graph,
            target_to_block,
        }
    }

    /// Iterate over all block indices
    pub fn blocks(&self) -> impl Iterator<Item = BlockIndex> {
        self.graph.node_indices()
    }

    /// Get the number of blocks
    #[cfg(test)]
    pub fn block_count(&self) -> usize {
        self.graph.node_count()
    }

    /// Get the number of blocks with back-edges
    #[cfg(test)]
    pub fn back_edge_count(&self) -> usize {
        self.blocks().filter(|&b| self.has_back_edge(b)).count()
    }

    /// Check if a block has a back-edge
    pub fn has_back_edge(&self, block: BlockIndex) -> bool {
        self.graph[block].back_edge_target.is_some()
    }

    /// Get the target of the back-edge (if any)
    pub fn back_edge_target(&self, block: BlockIndex) -> Option<&usize> {
        self.graph[block].back_edge_target.as_ref()
    }

    /// Get the index of the block's terminator instruction.
    ///
    /// Returns `Some(index)` if the block has an explicit terminator (branch or return),
    /// where index is derived from `instruction_range.end - 1`.
    /// Returns `None` if the block falls through without an explicit terminator.
    pub fn terminator_index(&self, block: BlockIndex) -> Option<usize> {
        let data = &self.graph[block];
        if data.has_explicit_terminator {
            // The terminator is always the last instruction in the block
            Some(data.instruction_range.end - 1)
        } else {
            None
        }
    }

    /// Get the number of actual instructions in a block
    pub fn instruction_count(&self, block: BlockIndex) -> usize {
        self.graph[block].instruction_count
    }

    /// Get the instruction range for a block
    pub fn instruction_range(&self, block: BlockIndex) -> &Range<usize> {
        &self.graph[block].instruction_range
    }

    /// Iterate over CFG successors of a block
    pub fn successors(&self, block: BlockIndex) -> impl Iterator<Item = BlockIndex> + '_ {
        self.graph.neighbors(block)
    }

    /// Get the call targets from a block (targets of `bl` instructions)
    pub fn call_targets(&self, block: BlockIndex) -> &[usize] {
        &self.graph[block].call_targets
    }

    /// Find all blocks not reachable from the given roots.
    ///
    /// `roots` contains instruction indices that identify BFS starting points.
    /// Any block whose start index matches a root becomes a BFS origin.
    pub fn compute_unreachable(&self, roots: &[usize]) -> Vec<BlockIndex> {
        let reachable = self.compute_reachable(roots);
        self.graph
            .node_indices()
            .filter(|node| !reachable.contains(node))
            .collect()
    }

    /// Computes all blocks reachable from the given roots via BFS.
    ///
    /// In addition to following CFG edges, this also follows `call_targets`
    /// (`bl` destinations) by resolving them through `target_to_block`.
    fn compute_reachable(&self, roots: &[usize]) -> HashSet<BlockIndex> {
        let mut reachable = HashSet::new();

        if self.graph.node_count() == 0 {
            return reachable;
        }

        // Seed the BFS queue with all root blocks.
        let root_set: HashSet<usize> = roots.iter().copied().collect();
        let mut queue = VecDeque::new();

        for node in self.graph.node_indices() {
            let start = self.instruction_range(node).start;
            if root_set.contains(&start) && reachable.insert(node) {
                queue.push_back(node);
            }
        }

        // BFS: follow both CFG edges and call targets.
        while let Some(node) = queue.pop_front() {
            // CFG successors (branches, fall-through)
            for successor in self.graph.neighbors(node) {
                if reachable.insert(successor) {
                    queue.push_back(successor);
                }
            }

            // Call targets (bl destinations) — resolve to blocks
            for &target in self.call_targets(node) {
                if let Some(&target_block) = self.target_to_block.get(&target) {
                    if reachable.insert(target_block) {
                        queue.push_back(target_block);
                    }
                }
            }
        }

        reachable
    }
}

#[cfg(test)]
mod tests {
    use crate::{build_block_graph, traits::mock_instruction::MockInstruction};

    #[test]
    fn test_empty_cfg_has_no_unreachable() {
        let instructions: Vec<MockInstruction> = vec![];
        let cfg = build_block_graph(&instructions);

        assert!(cfg.compute_unreachable(&[0]).is_empty());
    }

    #[test]
    fn test_single_block_all_reachable() {
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::new("sub", 1),
            MockInstruction::new("ret", 2),
        ];
        let cfg = build_block_graph(&instructions);

        assert_eq!(cfg.block_count(), 1);
        assert!(cfg.compute_unreachable(&[0]).is_empty());
    }

    #[test]
    fn test_linear_code_all_reachable() {
        // Multiple blocks connected via fall-through
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::with_target("b.lt", 1, 3), // conditional branch forward
            MockInstruction::new("mul", 2),
            MockInstruction::new("ret", 3),
        ];
        let cfg = build_block_graph(&instructions);

        // Blocks: [add, b.lt], [mul], [ret]
        assert_eq!(cfg.block_count(), 3);
        assert!(cfg.compute_unreachable(&[0]).is_empty());
    }

    #[test]
    fn test_unreachable_after_unconditional_branch() {
        // Code after unconditional branch is unreachable
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::with_target("b", 1, 100), // unconditional branch away
            MockInstruction::new("sub", 2),            // unreachable
            MockInstruction::new("mul", 3),
        ];
        let cfg = build_block_graph(&instructions);

        // Blocks: [add, b], [sub, mul]
        // Second block is unreachable (no edge from first block)
        assert_eq!(cfg.block_count(), 2);

        let unreachable = cfg.compute_unreachable(&[0]);
        assert_eq!(unreachable.len(), 1);

        // Verify the unreachable block is the one starting at index 2
        let unreachable_block = unreachable[0];
        assert_eq!(cfg.instruction_range(unreachable_block).start, 2);
    }

    #[test]
    fn test_unreachable_after_return() {
        // Code after return is unreachable
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::new("ret", 1),
            MockInstruction::new("sub", 2), // unreachable
            MockInstruction::new("mul", 3),
        ];
        let cfg = build_block_graph(&instructions);

        // Blocks: [add, ret], [sub, mul]
        assert_eq!(cfg.block_count(), 2);

        let unreachable = cfg.compute_unreachable(&[0]);
        assert_eq!(unreachable.len(), 1);

        let unreachable_block = unreachable[0];
        assert_eq!(cfg.instruction_range(unreachable_block).start, 2);
    }

    #[test]
    fn test_call_rescues_unreachable_block() {
        // Two "functions": func1 calls func2, func2 starts after func1's ret.
        // The bl instruction makes func2 reachable via call_targets.
        let instructions = vec![
            MockInstruction::with_target("bl", 0, 2), // call func2
            MockInstruction::new("ret", 1),
            MockInstruction::new("sub", 2), // func2 entry
            MockInstruction::new("ret", 3),
        ];
        let cfg = build_block_graph(&instructions);

        // With only root at 0, func2 is reachable via call edge
        let unreachable = cfg.compute_unreachable(&[0]);
        assert!(
            unreachable.is_empty(),
            "func2 should be reachable via bl call target"
        );
    }

    #[test]
    fn test_call_transitive_reachability() {
        // func1 calls func2 via bl; func2 branches to func3.
        // All three should be reachable from root 0.
        let instructions = vec![
            MockInstruction::with_target("bl", 0, 2), // call func2
            MockInstruction::new("ret", 1),
            MockInstruction::with_target("b.lt", 2, 4), // func2: branch to func3
            MockInstruction::new("sub", 3),
            MockInstruction::new("mul", 4), // func3 entry
            MockInstruction::new("ret", 5),
        ];
        let cfg = build_block_graph(&instructions);

        let unreachable = cfg.compute_unreachable(&[0]);
        assert!(
            unreachable.is_empty(),
            "func3 should be transitively reachable via func2: unreachable = {:?}",
            unreachable
                .iter()
                .map(|b| cfg.instruction_range(*b).clone())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_uncalled_function_remains_unreachable() {
        // Three functions. func1 calls func2 but NOT func3.
        // func3 should remain unreachable.
        let instructions = vec![
            MockInstruction::with_target("bl", 0, 2), // call func2 only
            MockInstruction::new("ret", 1),
            MockInstruction::new("sub", 2), // func2
            MockInstruction::new("ret", 3),
            MockInstruction::new("mul", 4), // func3 (uncalled)
            MockInstruction::new("ret", 5),
        ];
        let cfg = build_block_graph(&instructions);

        let unreachable = cfg.compute_unreachable(&[0]);
        assert_eq!(unreachable.len(), 1);
        assert_eq!(cfg.instruction_range(unreachable[0]).start, 4);
    }

    #[test]
    fn test_diamond_both_arms_reachable() {
        // if-else diamond: conditional branch to "else", fall-through to "then",
        // both merge at the end.
        let instructions = vec![
            MockInstruction::with_target("b.eq", 0, 3), // if eq, goto else
            MockInstruction::new("add", 1),             // then
            MockInstruction::with_target("b", 2, 4),    // jump to merge
            MockInstruction::new("sub", 3),             // else
            MockInstruction::new("ret", 4),             // merge
        ];
        let cfg = build_block_graph(&instructions);

        assert!(
            cfg.compute_unreachable(&[0]).is_empty(),
            "all arms of diamond should be reachable"
        );
    }

    #[test]
    fn test_loop_exit_reachable() {
        // Loop with conditional back-edge and fall-through exit
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::with_target("b.lt", 1, 0), // back-edge
            MockInstruction::new("ret", 2),             // loop exit
        ];
        let cfg = build_block_graph(&instructions);

        assert!(
            cfg.compute_unreachable(&[0]).is_empty(),
            "loop exit should be reachable via conditional fall-through"
        );
    }

    #[test]
    fn test_terminator_index_no_terminator() {
        // A block ending with a non-branch instruction has no explicit terminator
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::new("sub", 1),
            MockInstruction::new("mul", 2),
        ];
        let cfg = build_block_graph(&instructions);

        let block = cfg.blocks().next().unwrap();
        assert_eq!(cfg.terminator_index(block), None);
    }

    #[test]
    fn test_successors() {
        // Conditional branch creates two successors: target and fall-through
        let instructions = vec![
            MockInstruction::with_target("b.eq", 0, 2), // branch to index 2
            MockInstruction::new("add", 1),             // fall-through block
            MockInstruction::new("ret", 2),             // branch target block
        ];
        let cfg = build_block_graph(&instructions);

        let first_block = cfg.blocks().next().unwrap();
        let successors: Vec<_> = cfg.successors(first_block).collect();
        assert_eq!(
            successors.len(),
            2,
            "conditional branch should have 2 successors"
        );
    }
}
