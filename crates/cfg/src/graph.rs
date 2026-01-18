//! CFG data structures

use std::{
    collections::{HashMap, HashSet},
    ops::Range,
};

pub type BlockIndex = petgraph::graph::NodeIndex;

pub(crate) type Graph = petgraph::graph::DiGraph<BlockData, ()>;

/// Data stored in each basic block node
#[derive(Debug)]
pub struct BlockData {
    /// Target identifier at the start of this block (instruction index or byte offset)
    pub label: Option<usize>,

    /// Range of indices into the original instruction list.
    /// E.g., for a block containing instructions 3, 4, 5 this would be `3..6`
    pub instruction_range: Range<usize>,

    /// Branch target of the back-edge, if this block ends with one.
    pub back_edge_target: Option<usize>,

    /// Index of the block's terminator instruction (branch or return).
    /// `None` if the block falls through without an explicit terminator.
    pub terminator_index: Option<usize>,

    /// Number of actual instructions in this block
    pub instruction_count: usize,
}

/// Control flow graph backed by petgraph
pub struct Cfg {
    /// The underlying directed graph
    graph: Graph,
    /// Map from target (instruction index or byte offset) to block node
    target_to_block: HashMap<usize, BlockIndex>,
}

impl Cfg {
    /// Create a new CFG from components (used by builder)
    pub(crate) fn new(graph: Graph, target_to_block: HashMap<usize, BlockIndex>) -> Self {
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
    pub fn block_count(&self) -> usize {
        self.graph.node_count()
    }

    /// Get block by target (instruction index or byte offset)
    pub fn block_by_target(&self, target: &usize) -> Option<BlockIndex> {
        self.target_to_block.get(target).copied()
    }

    /// Check if a block has a back-edge
    pub fn has_back_edge(&self, block: BlockIndex) -> bool {
        self.graph[block].back_edge_target.is_some()
    }

    /// Get the target of the back-edge (if any)
    pub fn back_edge_target(&self, block: BlockIndex) -> Option<&usize> {
        self.graph[block].back_edge_target.as_ref()
    }

    /// Get the index of the block's terminator instruction
    pub fn terminator_index(&self, block: BlockIndex) -> Option<usize> {
        self.graph[block].terminator_index
    }

    /// Get the number of actual instructions in a block
    pub fn instruction_count(&self, block: BlockIndex) -> usize {
        self.graph[block].instruction_count
    }

    /// Get the instruction range for a block
    pub fn instruction_range(&self, block: BlockIndex) -> &Range<usize> {
        &self.graph[block].instruction_range
    }

    /// Get all blocks reachable from the entry point (first block)
    pub fn reachable_blocks(&self) -> HashSet<BlockIndex> {
        let mut reachable = HashSet::new();

        if self.graph.node_count() == 0 {
            return reachable;
        }

        // Entry point is the first block (node index 0)
        let entry = BlockIndex::new(0);
        let mut bfs = petgraph::visit::Bfs::new(&self.graph, entry);

        while let Some(node) = bfs.next(&self.graph) {
            reachable.insert(node);
        }

        reachable
    }

    /// Get all unreachable blocks (blocks not reachable from entry)
    pub fn unreachable_blocks(&self) -> Vec<BlockIndex> {
        let reachable = self.reachable_blocks();
        self.graph
            .node_indices()
            .filter(|node| !reachable.contains(node))
            .collect()
    }
}
