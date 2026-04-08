// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! The `Assembly` output type and post-processing helpers.

use std::{fmt, ops::Deref};

/// Assembly output from the compiler.
pub struct Assembly(String);

impl Assembly {
    pub(crate) fn new(asm: String) -> Self {
        Self(asm)
    }

    /// Strip `.subsections_via_symbols` — Mach-O's dead-stripping directive
    /// that prevents the assembler from encoding `tbz`/`tbnz` branch-to-label
    /// (the assembler can't guarantee range when subsections may be reordered).
    ///
    /// Called by the pipeline before instrumentation. Does NOT add trampoline
    /// aliases, so the output is safe to instrument and verify without false
    /// back-edges.
    pub fn strip_subsections(&mut self) {
        let asm = &self.0;
        let mut output = String::with_capacity(asm.len());
        for line in asm.lines() {
            if line.trim() == ".subsections_via_symbols" {
                continue;
            }
            output.push_str(line);
            output.push('\n');
        }
        self.0 = output;
    }

    /// Post-process: strip `.subsections_via_symbols` and add platform-compatible
    /// symbol aliases.
    ///
    /// On macOS (where LLVM emits `_name` symbols), adds unprefixed aliases
    /// so that instrumenter and the runtime can find functions by their
    /// Move names. On Linux, adds underscore-prefixed aliases for the same
    /// cross-platform compatibility.
    ///
    /// The trampoline aliases (`b _name`) create backward branches that look
    /// like back-edges to the verifier. Use [`Self::strip_subsections`] instead
    /// when the output will go through the full pipeline.
    pub fn add_symbol_aliases(&mut self) {
        self.strip_subsections();

        let mut global_names: Vec<String> = Vec::new();
        for line in self.0.lines() {
            let trimmed = line.trim();
            if let Some(name) = trimmed
                .strip_prefix(".globl\t")
                .or_else(|| trimmed.strip_prefix(".globl "))
            {
                global_names.push(name.trim().to_string());
            }
        }

        if !global_names.is_empty() {
            self.0.push('\n');
            for name in &global_names {
                if let Some(bare) = name.strip_prefix('_') {
                    // macOS: _add exists, add alias for bare name
                    self.0.push_str(&format!(".globl {bare}\n"));
                    self.0.push_str(&format!("{bare}:\n"));
                    self.0.push_str(&format!("\tb {name}\n"));
                } else {
                    // Linux: add exists, add alias for _name
                    self.0.push_str(&format!(".globl _{name}\n"));
                    self.0.push_str(&format!("_{name}:\n"));
                    self.0.push_str(&format!("\tb {name}\n"));
                }
            }
        }
    }
}

impl AsRef<[u8]> for Assembly {
    fn as_ref(&self) -> &[u8] {
        self.0.as_bytes()
    }
}

impl Deref for Assembly {
    type Target = str;

    fn deref(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Assembly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;

    use super::Assembly;

    #[test]
    fn strip_subsections_removes_directive() {
        let mut asm = Assembly(
            indoc! {"
                .globl\t_foo
                _foo:
                \tret
                .subsections_via_symbols
            "}
            .into(),
        );
        asm.strip_subsections();
        assert!(!asm.contains("subsections_via_symbols"));
    }

    #[test]
    fn strip_subsections_preserves_content() {
        let input = indoc! {"
            .section\t__TEXT,__text
            .globl\t_foo
            .p2align\t2
            _foo:
            \tmov x0, #42
            \tret
            .subsections_via_symbols
        "};
        let mut asm = Assembly(input.into());
        asm.strip_subsections();

        assert!(asm.contains(".section\t__TEXT,__text"));
        assert!(asm.contains(".globl\t_foo"));
        assert!(asm.contains("_foo:"));
        assert!(asm.contains("\tmov x0, #42"));
        assert!(asm.contains("\tret"));
    }

    #[test]
    fn strip_subsections_does_not_add_aliases() {
        let mut asm = Assembly(
            indoc! {"
                .globl\t_foo
                _foo:
                \tret
                .subsections_via_symbols
            "}
            .into(),
        );
        asm.strip_subsections();
        assert!(!asm.contains("\tb _foo"));
        assert!(!asm.contains("foo:\n\tb"));
    }

    #[test]
    fn strip_subsections_noop_when_absent() {
        let input = ".globl\t_foo\n_foo:\n\tret\n";
        let mut asm = Assembly(input.into());
        asm.strip_subsections();
        assert_eq!(&*asm, input);
    }

    #[test]
    fn aliases_macos_underscore_prefix() {
        let mut asm = Assembly(
            indoc! {"
                .globl\t_foo
                _foo:
                \tmov x0, #42
                \tret
            "}
            .into(),
        );
        asm.add_symbol_aliases();
        assert!(asm.contains(".globl foo\n"));
        assert!(asm.contains("foo:\n\tb _foo\n"));
    }

    #[test]
    fn aliases_linux_bare_name() {
        let mut asm = Assembly(
            indoc! {"
                .globl\tfoo
                foo:
                \tmov x0, #42
                \tret
            "}
            .into(),
        );
        asm.add_symbol_aliases();
        assert!(asm.contains(".globl _foo\n"));
        assert!(asm.contains("_foo:\n\tb foo\n"));
    }

    #[test]
    fn aliases_also_strips_subsections() {
        let mut asm = Assembly(
            indoc! {"
                .globl\t_foo
                _foo:
                \tret
                .subsections_via_symbols
            "}
            .into(),
        );
        asm.add_symbol_aliases();
        assert!(!asm.contains("subsections_via_symbols"));
    }

    #[test]
    fn aliases_no_globals_no_trampolines() {
        let mut asm = Assembly(
            indoc! {"
                ; just a comment
                \tmov x0, #1
                \tret
            "}
            .into(),
        );
        asm.add_symbol_aliases();
        assert!(!asm.contains(".globl"));
        assert!(!asm.contains("\tb "));
    }

    #[test]
    fn aliases_globl_with_space_separator() {
        let mut asm = Assembly(".globl _bar\n_bar:\n\tret\n".into());
        asm.add_symbol_aliases();
        assert!(asm.contains(".globl bar\n"));
        assert!(asm.contains("bar:\n\tb _bar\n"));
    }

    #[test]
    fn aliases_multiple_globals() {
        let mut asm = Assembly(
            indoc! {"
                .globl\t_alpha
                .globl\t_beta
                _alpha:
                \tret
                _beta:
                \tret
            "}
            .into(),
        );
        asm.add_symbol_aliases();
        assert!(asm.contains(".globl alpha\n"));
        assert!(asm.contains("alpha:\n\tb _alpha\n"));
        assert!(asm.contains(".globl beta\n"));
        assert!(asm.contains("beta:\n\tb _beta\n"));
    }
}
