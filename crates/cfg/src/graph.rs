//! CFG data structures

use std::{collections::HashSet, ops::Range};

pub type BlockIndex = petgraph::graph::NodeIndex;

pub(crate) type Graph = petgraph::graph::DiGraph<BlockData, ()>;

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
}

/// Control flow graph backed by petgraph
pub struct Cfg {
    /// The underlying directed graph
    graph: Graph,
}

impl Cfg {
    /// Create a new CFG from graph (used by builder)
    pub(crate) fn new(graph: Graph) -> Self {
        Self { graph }
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

    /// Find all blocks not reachable from the entry point.
    /// Performs a BFS traversal - O(V + E).
    pub fn find_unreachable_blocks(&self) -> Vec<BlockIndex> {
        let reachable = self.compute_reachable();
        self.graph
            .node_indices()
            .filter(|node| !reachable.contains(node))
            .collect()
    }

    /// Computes all blocks reachable from the entry point via BFS.
    /// BlockIndex 0 is the entry point by construction: the CFG builder
    /// always creates the first block for the function's first instruction.
    fn compute_reachable(&self) -> HashSet<BlockIndex> {
        let mut reachable = HashSet::new();

        if self.graph.node_count() == 0 {
            return reachable;
        }

        let entry = BlockIndex::new(0);
        let mut bfs = petgraph::visit::Bfs::new(&self.graph, entry);

        while let Some(node) = bfs.next(&self.graph) {
            reachable.insert(node);
        }

        reachable
    }
}

#[cfg(test)]
mod tests {
    use crate::{build_cfg, traits::mock_instruction::MockInstruction};

    #[test]
    fn test_empty_cfg_has_no_unreachable() {
        let instructions: Vec<MockInstruction> = vec![];
        let cfg = build_cfg(&instructions);

        assert!(cfg.find_unreachable_blocks().is_empty());
    }

    #[test]
    fn test_single_block_all_reachable() {
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::new("sub", 1),
            MockInstruction::new("ret", 2),
        ];
        let cfg = build_cfg(&instructions);

        assert_eq!(cfg.block_count(), 1);
        assert!(cfg.find_unreachable_blocks().is_empty());
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
        let cfg = build_cfg(&instructions);

        // Blocks: [add, b.lt], [mul], [ret]
        assert_eq!(cfg.block_count(), 3);
        assert!(cfg.find_unreachable_blocks().is_empty());
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
        let cfg = build_cfg(&instructions);

        // Blocks: [add, b], [sub, mul]
        // Second block is unreachable (no edge from first block)
        assert_eq!(cfg.block_count(), 2);

        let unreachable = cfg.find_unreachable_blocks();
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
        let cfg = build_cfg(&instructions);

        // Blocks: [add, ret], [sub, mul]
        assert_eq!(cfg.block_count(), 2);

        let unreachable = cfg.find_unreachable_blocks();
        assert_eq!(unreachable.len(), 1);

        let unreachable_block = unreachable[0];
        assert_eq!(cfg.instruction_range(unreachable_block).start, 2);
    }
}
