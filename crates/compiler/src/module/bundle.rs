// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Load pre-compiled Move modules (`.mv` files) and compile them through
//! the full pipeline. Used by integration tests for both individual `.mv`
//! files and the Sui framework.

use std::path::Path;

use move_binary_format::CompiledModule;

use crate::target::Target;
use crate::{ModuleInfo, assembly::Assembly};

/// A collection of deserialized Move modules that can be compiled one at a
/// time, using the rest as dependencies.
///
/// Modules loaded via `from_dir` are *targets* — searchable by `compile`.
/// Modules loaded via `with_dependencies_from_dir` are *deps only*.
pub struct ModuleBundle {
    targets: Vec<CompiledModule>,
    deps: Vec<CompiledModule>,
}

impl ModuleBundle {
    /// Load and deserialize all `.mv` files from a directory as targets.
    pub fn from_dir(dir: impl AsRef<Path>) -> Self {
        Self {
            targets: Self::load_mv_files(dir),
            deps: Vec::new(),
        }
    }

    /// Load additional `.mv` files from a directory as dependencies only
    /// (not searchable by `compile`).
    pub fn with_dependencies_from_dir(mut self, dir: impl AsRef<Path>) -> Self {
        self.deps.extend(Self::load_mv_files(dir));
        self
    }

    /// Find the named module among targets, compile it with all other
    /// targets and deps as dependencies, and return the assembly output.
    /// Uses the host architecture. Panics if the module is not found or
    /// compilation fails.
    pub fn compile(&self, module_name: &str) -> Assembly {
        self.compile_for_target(module_name, &Target::host())
    }

    /// Like [`compile`](Self::compile) but for an explicit [`Target`].
    pub fn compile_for_target(&self, module_name: &str, target: &Target) -> Assembly {
        let module_idx = self
            .targets
            .iter()
            .position(|m| m.self_id().name().as_str() == module_name)
            .unwrap_or_else(|| panic!("module {module_name} not found"));

        let module = &self.targets[module_idx];
        let dependencies: Vec<_> = self
            .targets
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != module_idx)
            .map(|(_, m)| m.clone())
            .chain(self.deps.iter().cloned())
            .collect();

        crate::compile_module_with_deps(target, module, &dependencies)
            .unwrap_or_else(|e| panic!("{module_name} compilation failed: {e}"))
    }

    /// Return the mangled symbol names for all non-native, non-generic
    /// functions in the named module.
    ///
    /// This is a *conservative* subset of what the compiler actually emits:
    ///
    /// - **Checked**: non-native functions with zero type parameters.
    /// - **Not checked**: phantom-only generic functions (the compiler does
    ///   emit these, but detecting phantom params requires the full Move
    ///   model — overkill for a test helper).
    /// - **Not checked**: monomorphized generic instances (`foo$u64`) which
    ///   depend on call-site analysis across the whole module.
    /// - **Not checked**: correctness of the function body, `ret` per
    ///   function, or cross-module call resolution.
    pub fn expected_symbols(&self, module_name: &str) -> Vec<String> {
        let module = self
            .targets
            .iter()
            .find(|m| m.self_id().name().as_str() == module_name)
            .unwrap_or_else(|| panic!("module {module_name} not found"));

        ModuleInfo::from_module(module)
            .unwrap_or_else(|e| panic!("{module_name}: {e}"))
            .functions
            .iter()
            .filter(|f| !f.is_native && !f.is_generic)
            .map(|f| f.symbol.clone())
            .collect()
    }

    /// Compile the named module and verify every expected non-native,
    /// non-generic function appears as a symbol in the assembly output.
    ///
    /// Also checks that at least one `ret` instruction exists when there
    /// are compiled functions (i.e., we produced real function bodies).
    pub fn compile_checked(&self, module_name: &str, target: &Target) -> Assembly {
        let asm = self.compile_for_target(module_name, target);
        let symbols = self.expected_symbols(module_name);
        for sym in &symbols {
            assert!(
                asm.contains(sym),
                "{module_name}: expected symbol `{sym}` not found in assembly"
            );
        }
        if !symbols.is_empty() {
            assert!(
                asm.contains("\tret"),
                "{module_name}: no `ret` instruction found in assembly"
            );
        }
        asm
    }

    fn load_mv_files(dir: impl AsRef<Path>) -> Vec<CompiledModule> {
        let mut modules = Vec::new();
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().is_some_and(|e| e == "mv") {
                let bytes = std::fs::read(&path).unwrap();
                modules.push(CompiledModule::deserialize_with_defaults(&bytes).unwrap());
            }
        }
        modules
    }
}
