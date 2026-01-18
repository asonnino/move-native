//! CFG data structures
//!
//! Generic CFG types parameterized by instruction type.

use std::{collections::HashMap, ops::Range};

use petgraph::graph::{DiGraph, NodeIndex};

use crate::InstructionInfo;

/// Data stored in each basic block node
#[derive(Debug)]
pub struct BlockData<I: InstructionInfo> {
    /// Label/target at the start of this block (if any)
    pub label: Option<I::Target>,

    /// Range of indices into the original instruction list.
    /// E.g., for a block containing instructions 3, 4, 5 this would be `3..6`
    pub instruction_range: Range<usize>,

    /// Branch target of the back-edge (label or offset), if this block ends with one.
    pub back_edge_target: Option<I::Target>,

    /// Index of the block's terminator instruction (branch or return).
    /// `None` if the block falls through without an explicit terminator.
    pub terminator_index: Option<usize>,

    /// Number of actual instructions in this block
    pub instruction_count: usize,
}

/// Control flow graph backed by petgraph
pub struct Cfg<I: InstructionInfo> {
    /// The underlying directed graph
    graph: DiGraph<BlockData<I>, ()>,
    /// Map from target (label or offset) to block node
    target_to_block: HashMap<I::Target, NodeIndex>,
}

impl<I: InstructionInfo> Cfg<I> {
    /// Create a new CFG from components (used by builder)
    pub(crate) fn new(
        graph: DiGraph<BlockData<I>, ()>,
        target_to_block: HashMap<I::Target, NodeIndex>,
    ) -> Self {
        Self {
            graph,
            target_to_block,
        }
    }

    /// Iterate over all block indices
    pub fn blocks(&self) -> impl Iterator<Item = NodeIndex> + '_ {
        self.graph.node_indices()
    }

    /// Get the number of blocks
    pub fn block_count(&self) -> usize {
        self.graph.node_count()
    }

    /// Get block by target (label string or byte offset)
    pub fn block_by_target(&self, target: &I::Target) -> Option<NodeIndex> {
        self.target_to_block.get(target).copied()
    }

    /// Check if a block has a back-edge
    pub fn has_back_edge(&self, block: NodeIndex) -> bool {
        self.graph[block].back_edge_target.is_some()
    }

    /// Get the target of the back-edge (if any)
    pub fn back_edge_target(&self, block: NodeIndex) -> Option<&I::Target> {
        self.graph[block].back_edge_target.as_ref()
    }

    /// Get the index of the block's terminator instruction
    pub fn terminator_index(&self, block: NodeIndex) -> Option<usize> {
        self.graph[block].terminator_index
    }

    /// Get the number of actual instructions in a block
    pub fn instruction_count(&self, block: NodeIndex) -> usize {
        self.graph[block].instruction_count
    }
}
