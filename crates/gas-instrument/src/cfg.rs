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
    algo::dominators,
    graph::{DiGraph, NodeIndex},
};

use crate::parser::ParsedLine;

/// Data stored in each basic block node
#[derive(Debug)]
pub struct BlockData {
    /// Label at the start of this block (if any)
    pub label: Option<String>,

    /// Range of indices into the original parsed lines.
    /// E.g., for a block containing lines 3, 4, 5 this would be `3..6`
    pub line_indices: Range<usize>,

    /// Target block of the back-edge, if this block ends with one.
    /// Use `Cfg::back_edge_target_label()` to get the label string for assembly emission.
    pub back_edge_target: Option<NodeIndex>,

    /// Line index of the block's terminator: the branch (`b`, `b.cond`, `cbz`, etc.)
    /// or return (`ret`) instruction that ends control flow in this block.
    /// `None` if the block falls through without an explicit terminator.
    pub terminator_line: Option<usize>,

    /// Number of actual instructions in this block (excluding directives, labels, empty lines)
    pub instruction_count: usize,
}

/// Control flow graph backed by petgraph
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

    /// Get block by label
    pub fn block_by_label(&self, label: &str) -> Option<NodeIndex> {
        self.label_to_block.get(label).copied()
    }

    /// Get successors of a block
    #[cfg(test)]
    pub fn successors(&self, idx: NodeIndex) -> impl Iterator<Item = NodeIndex> + '_ {
        self.graph.neighbors(idx)
    }

    /// Get the label of the back-edge target (for assembly emission)
    pub fn back_edge_target_label(&self, block: NodeIndex) -> Option<&str> {
        self.graph[block]
            .back_edge_target
            .and_then(|target| self.graph[target].label.as_deref())
    }

    /// Get the line index of the block's terminator (branch or return)
    pub fn terminator_line(&self, block: NodeIndex) -> Option<usize> {
        self.graph[block].terminator_line
    }

    /// Get the number of actual instructions in a block (excluding directives, labels, empty lines)
    pub fn instruction_count(&self, block: NodeIndex) -> usize {
        self.graph[block].instruction_count
    }

    /// Check if a label exists in the CFG
    pub fn has_label(&self, label: &str) -> bool {
        self.label_to_block.contains_key(label)
    }

    /// Check if a block has a back-edge
    pub fn has_back_edge(&self, block: NodeIndex) -> bool {
        self.graph[block].back_edge_target.is_some()
    }
}

/// Build a CFG from parsed assembly lines
pub fn build(lines: &[ParsedLine]) -> Cfg {
    CfgBuilder::new(lines).build()
}

/// Builder for constructing a CFG from parsed assembly lines
struct CfgBuilder<'a> {
    lines: &'a [ParsedLine<'a>],
    graph: DiGraph<BlockData, ()>,
    label_to_block: HashMap<String, NodeIndex>,
    nodes: Vec<NodeIndex>,
}

impl<'a> CfgBuilder<'a> {
    fn new(lines: &'a [ParsedLine<'a>]) -> Self {
        Self {
            lines,
            graph: DiGraph::new(),
            label_to_block: HashMap::new(),
            nodes: Vec::new(),
        }
    }

    fn build(mut self) -> Cfg {
        let block_starts = self.find_block_boundaries();
        self.create_blocks(&block_starts);
        self.add_edges();
        self.identify_back_edges();

        Cfg {
            graph: self.graph,
            label_to_block: self.label_to_block,
        }
    }

    /// Find basic block boundaries.
    /// A new block starts at:
    /// - The beginning of the file
    /// - Any label
    /// - The instruction after a branch
    fn find_block_boundaries(&self) -> Vec<usize> {
        let mut block_starts = Vec::new();
        let mut previous_was_branch = false;

        for (idx, line) in self.lines.iter().enumerate() {
            let is_start = idx == 0 || line.label.is_some() || previous_was_branch;

            if is_start && self.has_code_at(idx) {
                block_starts.push(idx);
            }

            previous_was_branch = line
                .instruction
                .as_ref()
                .is_some_and(|i| i.is_branch() || i.is_return());
        }

        block_starts
    }

    /// Create graph nodes for each basic block.
    fn create_blocks(&mut self, block_starts: &[usize]) {
        for (block_idx, &start_idx) in block_starts.iter().enumerate() {
            let end_idx = block_starts
                .get(block_idx + 1)
                .copied()
                .unwrap_or(self.lines.len());

            let line_indices = start_idx..end_idx;
            let label = self.lines[start_idx].label.map(|s| s.to_string());

            let instruction_count = line_indices
                .clone()
                .filter(|&idx| self.lines[idx].instruction.is_some())
                .count();

            let node = self.graph.add_node(BlockData {
                label,
                line_indices: line_indices.clone(),
                back_edge_target: None,
                terminator_line: None,
                instruction_count,
            });
            self.nodes.push(node);

            // Register all labels in this block
            for idx in line_indices {
                if let Some(lbl) = self.lines[idx].label {
                    self.label_to_block.insert(lbl.to_string(), node);
                }
            }
        }
    }

    /// Add edges based on control flow and record terminator lines.
    fn add_edges(&mut self) {
        for (block_idx, &node) in self.nodes.iter().enumerate() {
            let block = &self.graph[node];

            let terminator = block
                .line_indices
                .clone()
                .rev()
                .find(|&idx| self.lines[idx].instruction.is_some());

            if let Some(terminator_line) = terminator {
                let instruction = self.lines[terminator_line].instruction.as_ref().unwrap();

                if instruction.is_branch() || instruction.is_return() {
                    self.graph[node].terminator_line = Some(terminator_line);
                }

                if instruction.is_branch() && !instruction.is_call() {
                    if let Some(target) = instruction.get_branch_target() {
                        if let Some(&target_node) = self.label_to_block.get(target) {
                            self.graph.add_edge(node, target_node, ());
                        }
                    }
                }

                if !instruction.is_return() && !instruction.is_unconditional_jump() {
                    if let Some(&next_node) = self.nodes.get(block_idx + 1) {
                        self.graph.add_edge(node, next_node, ());
                    }
                }
            } else if let Some(&next_node) = self.nodes.get(block_idx + 1) {
                self.graph.add_edge(node, next_node, ());
            }
        }
    }

    /// Compute dominators and mark back-edges.
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

        for (node, target) in back_edges {
            debug_assert!(
                self.graph[node].instruction_count > 0,
                "back-edge should have instructions"
            );
            self.graph[node].back_edge_target = Some(target);
        }
    }

    /// Check if there's any code at or after this position before the next label.
    fn has_code_at(&self, idx: usize) -> bool {
        if self.lines[idx].instruction.is_some() {
            return true;
        }

        self.lines
            .iter()
            .skip(idx + 1)
            .take_while(|line| line.label.is_none())
            .any(|line| line.instruction.is_some())
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;

    use crate::{cfg, parser, parser::ParsedLine, Cfg};

    /// Helper to reduce test boilerplate: parses assembly and builds CFG
    fn build_cfg(input: &str) -> (Cfg, Vec<ParsedLine>) {
        let lines = parser::parse(input);
        let cfg = cfg::build(&lines);
        (cfg, lines)
    }

    #[test]
    fn test_empty_input() {
        let (cfg, _) = build_cfg("");
        assert_eq!(cfg.block_count(), 0);
    }

    #[test]
    fn test_single_ret() {
        let (cfg, _) = build_cfg(indoc! {"
            _minimal:
                ret
        "});

        assert_eq!(cfg.block_count(), 1);
        let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
        assert_eq!(back_edge_count, 0);
    }

    #[test]
    fn test_linear_code_no_loops() {
        let (cfg, _) = build_cfg(indoc! {"
            _linear:
                mov x0, #1
                add x0, x0, #2
                mul x0, x0, #3
                ret
        "});

        let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
        assert_eq!(back_edge_count, 0, "Linear code should have no back-edges");
        assert_eq!(cfg.block_count(), 1, "Linear code should be one block");
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
    fn test_block_by_label() {
        let (cfg, _) = build_cfg(indoc! {"
            _start:
                mov x0, #0
            .Lmiddle:
                add x0, x0, #1
            .Lend:
                ret
        "});

        assert!(cfg.block_by_label("_start").is_some());
        assert!(cfg.block_by_label(".Lmiddle").is_some());
        assert!(cfg.block_by_label(".Lend").is_some());
        assert!(cfg.block_by_label(".Lnonexistent").is_none());

        // Different labels should (generally) be different blocks
        let start = cfg.block_by_label("_start").unwrap();
        let middle = cfg.block_by_label(".Lmiddle").unwrap();
        assert_ne!(start, middle);
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
    fn test_instruction_count() {
        let (cfg, _) = build_cfg(indoc! {"
            _func:
                mov x0, #0
                mov x1, #1
                add x0, x0, x1
            .Lloop:
                sub x0, x0, #1
                cbnz x0, .Lloop
                ret
        "});

        let entry = cfg.block_by_label("_func").unwrap();
        let loop_block = cfg.block_by_label(".Lloop").unwrap();

        assert_eq!(
            cfg.instruction_count(entry),
            3,
            "Entry block should have 3 instructions"
        );
        // cbnz is a conditional branch, so it ends the block.
        // ret is in a separate fall-through block.
        assert_eq!(
            cfg.instruction_count(loop_block),
            2,
            "Loop block should have 2 instructions (sub, cbnz)"
        );
    }

    #[test]
    fn test_instruction_count_with_directives() {
        let (cfg, _) = build_cfg(indoc! {"
            .global _func
            .align 4
            _func:
                mov x0, #0
                .cfi_startproc
                add x0, x0, #1
                ret
        "});

        let func = cfg.block_by_label("_func").unwrap();
        // Should only count actual instructions, not directives
        assert_eq!(
            cfg.instruction_count(func),
            3,
            "Should count only instructions, not directives"
        );
    }

    #[test]
    fn test_terminator_line() {
        let (cfg, lines) = build_cfg(indoc! {"
            _func:
                mov x0, #0
                mov x1, #1
            .Lloop:
                add x0, x0, #1
                cmp x0, x1
                b.lt .Lloop
                ret
        "});

        let entry = cfg.block_by_label("_func").unwrap();
        let loop_block = cfg.block_by_label(".Lloop").unwrap();

        // Entry block falls through to .Lloop - no explicit terminator
        assert_eq!(
            cfg.terminator_line(entry),
            None,
            "Fall-through block should have no terminator"
        );

        // Loop block ends with b.lt (a branch)
        let loop_term = cfg.terminator_line(loop_block);
        assert!(loop_term.is_some(), "Loop block should have terminator");
        assert!(
            lines[loop_term.unwrap()]
                .instruction
                .as_ref()
                .unwrap()
                .is_branch(),
            "Loop terminator should be a branch"
        );

        // Find the block with ret and verify its terminator
        let ret_block = cfg.blocks().find(|&b| {
            cfg.terminator_line(b)
                .map(|idx| {
                    lines[idx]
                        .instruction
                        .as_ref()
                        .map(|i| i.is_return())
                        .unwrap_or(false)
                })
                .unwrap_or(false)
        });
        assert!(ret_block.is_some(), "Should find block with ret terminator");
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

        let back_edge_block = cfg.blocks().find(|&b| cfg.has_back_edge(b));
        assert!(back_edge_block.is_some());

        assert_eq!(
            cfg.back_edge_target_label(back_edge_block.unwrap()),
            Some(".Lloop")
        );
    }

    #[test]
    fn test_self_loop() {
        let (cfg, _) = build_cfg(indoc! {"
            _spin:
            .Lspin:
                b .Lspin
        "});

        let back_edge_block = cfg.blocks().find(|&b| cfg.has_back_edge(b));
        assert!(
            back_edge_block.is_some(),
            "Should detect self-loop back-edge"
        );
        assert_eq!(
            cfg.back_edge_target_label(back_edge_block.unwrap()),
            Some(".Lspin")
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

        let back_edge_block = cfg.blocks().find(|&b| cfg.has_back_edge(b));
        assert!(
            back_edge_block.is_some(),
            "Should detect do-while back-edge"
        );
        assert_eq!(
            cfg.back_edge_target_label(back_edge_block.unwrap()),
            Some(".Lbody")
        );
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

        let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
        assert_eq!(back_edge_count, 2, "Expected 2 back-edges for nested loops");

        let inner_be = cfg
            .blocks()
            .find(|&b| cfg.back_edge_target_label(b) == Some(".Linner"));
        let outer_be = cfg
            .blocks()
            .find(|&b| cfg.back_edge_target_label(b) == Some(".Louter"));
        assert!(inner_be.is_some(), "Should have back-edge to .Linner");
        assert!(outer_be.is_some(), "Should have back-edge to .Louter");
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

        let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
        assert_eq!(
            back_edge_count, 2,
            "Expected 2 back-edges for two independent loops"
        );

        let loop1_be = cfg
            .blocks()
            .find(|&b| cfg.back_edge_target_label(b) == Some(".Lloop1"));
        let loop2_be = cfg
            .blocks()
            .find(|&b| cfg.back_edge_target_label(b) == Some(".Lloop2"));
        assert!(loop1_be.is_some(), "Should have back-edge to .Lloop1");
        assert!(loop2_be.is_some(), "Should have back-edge to .Lloop2");
    }

    #[test]
    fn test_loop_with_break() {
        // Loop with early exit (break pattern)
        let (cfg, _) = build_cfg(indoc! {"
            _with_break:
                mov x0, #0
            .Lloop:
                add x0, x0, #1
                cmp x0, #5
                b.eq .Lbreak
                cmp x0, #10
                b.lt .Lloop
            .Lbreak:
                ret
        "});

        let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
        assert_eq!(back_edge_count, 1, "Should have exactly one back-edge");

        let back_edge_block = cfg
            .blocks()
            .find(|&b| cfg.back_edge_target_label(b) == Some(".Lloop"));
        assert!(back_edge_block.is_some());
    }

    #[test]
    fn test_loop_with_continue() {
        // Continue pattern: branch back to loop header from middle
        let (cfg, _) = build_cfg(indoc! {"
            _with_continue:
                mov x0, #0
            .Lloop:
                add x0, x0, #1
                tst x0, #1
                b.ne .Lloop
                add x1, x1, x0
                cmp x0, #10
                b.lt .Lloop
                ret
        "});

        // Should have 2 back-edges: one from b.ne and one from b.lt
        let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
        assert_eq!(
            back_edge_count, 2,
            "Should have two back-edges (continue and normal)"
        );
    }

    #[test]
    fn test_infinite_loop_with_conditional_break() {
        // while(true) { if (cond) break; }
        let (cfg, _) = build_cfg(indoc! {"
            _infinite:
            .Lloop:
                bl _do_work
                cbnz x0, .Ldone
                b .Lloop
            .Ldone:
                ret
        "});

        let back_edge_block = cfg
            .blocks()
            .find(|&b| cfg.back_edge_target_label(b) == Some(".Lloop"));
        assert!(
            back_edge_block.is_some(),
            "Should detect back-edge in infinite loop"
        );
    }

    #[test]
    fn test_cbz_loop() {
        let (cfg, _) = build_cfg(indoc! {"
            _cbz_loop:
                mov x0, #10
            .Lloop:
                sub x0, x0, #1
                cbnz x0, .Lloop
                ret
        "});

        let back_edge_block = cfg.blocks().find(|&b| cfg.has_back_edge(b));
        assert!(back_edge_block.is_some(), "Should detect cbnz back-edge");
        assert_eq!(
            cfg.back_edge_target_label(back_edge_block.unwrap()),
            Some(".Lloop")
        );
    }

    #[test]
    fn test_cbz_exit_loop() {
        // cbz used to exit loop (branch forward when zero)
        let (cfg, _) = build_cfg(indoc! {"
            _cbz_exit:
                mov x0, #10
            .Lloop:
                sub x0, x0, #1
                cbz x0, .Ldone
                b .Lloop
            .Ldone:
                ret
        "});

        let back_edge_block = cfg
            .blocks()
            .find(|&b| cfg.back_edge_target_label(b) == Some(".Lloop"));
        assert!(
            back_edge_block.is_some(),
            "Should detect back-edge from unconditional b"
        );
    }

    #[test]
    fn test_tbz_loop() {
        let (cfg, _) = build_cfg(indoc! {"
            _tbz_loop:
                mov x0, #0x80
            .Lloop:
                lsr x0, x0, #1
                tbnz x0, #0, .Lloop
                ret
        "});

        let back_edge_block = cfg.blocks().find(|&b| cfg.has_back_edge(b));
        assert!(back_edge_block.is_some(), "Should detect tbnz back-edge");
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

        let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
        assert_eq!(
            back_edge_count, 0,
            "Diamond pattern should have no back-edges"
        );
    }

    #[test]
    fn test_multiple_exit_points() {
        let (cfg, _) = build_cfg(indoc! {"
            _multi_exit:
                cmp x0, #0
                b.lt .Lerror
                cmp x0, #100
                b.gt .Lerror
                mov x0, #1
                ret
            .Lerror:
                mov x0, #0
                ret
        "});

        // No loops, just multiple exits
        let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
        assert_eq!(
            back_edge_count, 0,
            "Multiple exits should not create back-edges"
        );
    }

    #[test]
    fn test_consecutive_labels() {
        // Each label creates a block entry point, even if consecutive.
        // The CFG builder creates separate blocks for each label.
        let (cfg, _) = build_cfg(indoc! {"
            _func:
                cmp x0, #0
                b.eq .Lfirst
                mov x0, #1
                ret
            .Lfirst:
            .Lsecond:
            .Lthird:
                mov x0, #2
                ret
        "});

        // All three labels should exist and be findable
        assert!(cfg.has_label(".Lfirst"));
        assert!(cfg.has_label(".Lsecond"));
        assert!(cfg.has_label(".Lthird"));

        // Each label is registered - branch target resolution works
        assert!(cfg.block_by_label(".Lfirst").is_some());
        assert!(cfg.block_by_label(".Lsecond").is_some());
        assert!(cfg.block_by_label(".Lthird").is_some());
    }

    #[test]
    fn test_branch_to_function_start() {
        // Loop that branches back to the entry point
        let (cfg, _) = build_cfg(indoc! {"
            _entry:
                add x0, x0, #1
                cmp x0, #10
                b.lt _entry
                ret
        "});

        let back_edge_block = cfg
            .blocks()
            .find(|&b| cfg.back_edge_target_label(b) == Some("_entry"));
        assert!(
            back_edge_block.is_some(),
            "Should detect back-edge to function entry"
        );
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

        let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
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

        let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
        assert_eq!(
            back_edge_count, 0,
            "Recursive call should not create a back-edge"
        );
    }

    #[test]
    fn test_unreachable_loop_not_detected() {
        // Loop after unconditional ret is unreachable.
        // Dominator analysis won't find it as a back-edge (by design).
        let (cfg, _) = build_cfg(indoc! {"
            _func:
                mov x0, #1
                ret
            .Lunreachable:
                add x0, x0, #1
                b .Lunreachable
        "});

        // The unreachable loop should NOT be detected as a back-edge
        // because dominator analysis only works on reachable code
        let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
        assert_eq!(
            back_edge_count, 0,
            "Unreachable loop should not be detected as back-edge"
        );
    }

    #[test]
    fn test_unreachable_after_unconditional_branch() {
        let (cfg, _) = build_cfg(indoc! {"
            _func:
                b .Lend
            .Lunreachable:
                add x0, x0, #1
                b .Lunreachable
            .Lend:
                ret
        "});

        // The unreachable loop should NOT be detected
        let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
        assert_eq!(
            back_edge_count, 0,
            "Unreachable loop after unconditional branch should not be detected"
        );
    }

    #[test]
    fn test_back_edge_target_label() {
        let (cfg, _) = build_cfg(indoc! {"
            _test:
                mov x0, #0
            .Lloop:
                add x0, x0, #1
                b.lt .Lloop
                ret
        "});

        let back_edge_node = cfg.blocks().find(|&b| cfg.has_back_edge(b)).unwrap();

        // Verify the back-edge target label
        assert_eq!(cfg.back_edge_target_label(back_edge_node), Some(".Lloop"));

        // Verify we can get the target NodeIndex directly
        let target_idx = cfg.block(back_edge_node).back_edge_target.unwrap();
        assert_eq!(cfg.block(target_idx).label.as_deref(), Some(".Lloop"));
    }
}
