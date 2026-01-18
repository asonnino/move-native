//! Control Flow Graph for text assembly
//!
//! Re-exports from the `cfg` crate with text-assembly-specific helpers.

use crate::parser::{ParsedAssembly, ResolveError, ResolvedInstruction};

/// Result of building a CFG from parsed assembly
pub struct CfgResult {
    /// The control flow graph
    pub cfg: cfg::Cfg,
    /// The resolved instructions (for mapping back to line numbers)
    pub resolved: Vec<ResolvedInstruction>,
}

/// Build a CFG from parsed assembly
///
/// This resolves labels to instruction indices, then builds the CFG.
/// Returns the CFG and resolved instructions (needed to map instruction
/// indices back to line numbers for instrumentation).
///
/// Returns an error if label resolution fails (undefined labels, trailing labels).
pub fn build(asm: &ParsedAssembly<'_>) -> Result<CfgResult, ResolveError> {
    let resolved = asm.resolve()?;
    let cfg = cfg::build_cfg(&resolved);
    Ok(CfgResult { cfg, resolved })
}

// Re-export NodeIndex for convenience
pub use cfg::NodeIndex;

#[cfg(test)]
mod tests {
    use indoc::indoc;

    use super::*;
    use crate::parser::ParsedAssembly;

    #[test]
    fn test_empty_input() {
        let asm = ParsedAssembly::parse("");
        let result = build(&asm).unwrap();
        assert_eq!(result.cfg.block_count(), 0);
    }

    #[test]
    fn test_simple_loop() {
        let input = indoc! {"
            _func:
                mov x0, #0
            .Lloop:
                add x0, x0, #1
                cmp x0, #10
                b.lt .Lloop
                ret
        "};
        let asm = ParsedAssembly::parse(input);
        let result = build(&asm).unwrap();

        let back_edge_count = result
            .cfg
            .blocks()
            .filter(|&b| result.cfg.has_back_edge(b))
            .count();
        assert_eq!(back_edge_count, 1, "Should have exactly one back-edge");
    }

    #[test]
    fn test_nested_loops() {
        let input = indoc! {"
            _func:
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
        "};
        let asm = ParsedAssembly::parse(input);
        let result = build(&asm).unwrap();

        let back_edge_count = result
            .cfg
            .blocks()
            .filter(|&b| result.cfg.has_back_edge(b))
            .count();
        assert_eq!(back_edge_count, 2, "Should have two back-edges");
    }

    #[test]
    fn test_back_edge_target() {
        let input = indoc! {"
            _func:
            .Lloop:
                add x0, x0, #1
                b.lt .Lloop
                ret
        "};
        let asm = ParsedAssembly::parse(input);
        let result = build(&asm).unwrap();

        // After resolution:
        // - index 0: add (was .Lloop)
        // - index 1: b.lt (back-edge to index 0)
        // - index 2: ret
        let loop_block = result.cfg.block_by_target(&0).unwrap();
        assert_eq!(
            result.cfg.back_edge_target(loop_block),
            Some(&0) // back-edge targets instruction index 0
        );
    }
}
