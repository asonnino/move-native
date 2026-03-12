// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Load pre-compiled Move modules (`.mv` files) and compile them through
//! the full pipeline. Used by integration tests for both individual `.mv`
//! files and the Sui framework.

use std::path::Path;

use move_binary_format::CompiledModule;

use crate::assembly::Assembly;
use crate::target::Target;

/// A collection of deserialized Move modules that can be compiled one at a
/// time, using the rest as dependencies.
///
/// Modules loaded via `from_dir` / `from_bytes` are *targets* — searchable
/// by `compile`. Modules loaded via `with_deps_from_dir` are *deps only*.
pub struct ModuleFixture {
    targets: Vec<CompiledModule>,
    deps: Vec<CompiledModule>,
}

impl ModuleFixture {
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
    /// Panics if the module is not found or compilation fails.
    pub fn compile(&self, module_name: &str) -> Assembly {
        let target_idx = self
            .targets
            .iter()
            .position(|m| m.self_id().name().as_str() == module_name)
            .unwrap_or_else(|| panic!("module {module_name} not found"));

        let target = &self.targets[target_idx];
        let dependencies: Vec<_> = self
            .targets
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != target_idx)
            .map(|(_, m)| m.clone())
            .chain(self.deps.iter().cloned())
            .collect();

        crate::compile_module_with_deps(&Target::host(), target, &dependencies)
            .unwrap_or_else(|e| panic!("{module_name} compilation failed: {e}"))
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
