//! Control Flow Graph for text assembly
//!
//! Re-exports from the generic `cfg` crate with text-assembly-specific helpers.

use crate::parser::{IndexedParsedLine, ParsedLine};

/// Type alias for text assembly CFG
pub type Cfg = cfg::Cfg<IndexedParsedLine>;

/// Build a CFG from parsed assembly lines
pub fn build(lines: &[ParsedLine<'_>]) -> Cfg {
    let indexed = IndexedParsedLine::from_lines(lines);
    cfg::build_cfg(&indexed)
}

// Re-export NodeIndex for convenience
pub use cfg::NodeIndex;

#[cfg(test)]
mod tests {
    use indoc::indoc;

    use super::*;
    use crate::parser;

    #[test]
    fn test_empty_input() {
        let lines = parser::parse("");
        let cfg = build(&lines);
        assert_eq!(cfg.block_count(), 0);
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
        let lines = parser::parse(input);
        let cfg = build(&lines);

        let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
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
        let lines = parser::parse(input);
        let cfg = build(&lines);

        let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
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
        let lines = parser::parse(input);
        let cfg = build(&lines);

        let loop_block = cfg.block_by_target(&".Lloop".to_string()).unwrap();
        assert_eq!(
            cfg.back_edge_target(loop_block),
            Some(&".Lloop".to_string())
        );
    }
}