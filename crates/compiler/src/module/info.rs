// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Inspect a compiled Move module: list functions, their ABIs, and mangled symbols.

use move_binary_format::CompiledModule;
use move_binary_format::file_format::Visibility;

use crate::error::{CompileError, CompileResult};
use crate::mangle::Mangler;

/// Information about a single function in a Move module.
#[derive(Debug, Clone)]
pub struct FunctionInfo {
    /// Move function name (e.g., `"add"`).
    pub name: String,
    /// Mangled linker symbol (e.g., `"_mv_0x0_M_add"`).
    pub symbol: String,
    /// Number of parameters.
    pub arg_count: usize,
    /// Number of return values.
    pub ret_count: usize,
    /// Whether the function is declared `public`.
    pub is_public: bool,
    /// Whether the function is a native (no bytecode body).
    pub is_native: bool,
    /// Whether the function has type parameters (generics).
    pub is_generic: bool,
}

/// Metadata about a compiled Move module.
#[derive(Debug)]
pub struct ModuleInfo {
    /// Module address as a hex literal (e.g., `"0x0"`).
    pub address: String,
    /// Module name (e.g., `"M"`).
    pub name: String,
    /// All functions declared in the module.
    pub functions: Vec<FunctionInfo>,
}

impl ModuleInfo {
    /// Extract metadata from a compiled Move module.
    pub fn from_module(module: &CompiledModule) -> CompileResult<Self> {
        let self_handle = module
            .module_handles
            .get(module.self_module_handle_idx.0 as usize)
            .ok_or_else(|| CompileError::deserialize("invalid self_module_handle_idx"))?;

        let address = module
            .address_identifiers
            .get(self_handle.address.0 as usize)
            .ok_or_else(|| CompileError::deserialize("invalid address index"))?
            .to_hex_literal();

        let name = module
            .identifiers
            .get(self_handle.name.0 as usize)
            .ok_or_else(|| CompileError::deserialize("invalid module name index"))?
            .as_str()
            .to_string();

        let mut functions = Vec::new();
        for def in &module.function_defs {
            let handle = module
                .function_handles
                .get(def.function.0 as usize)
                .ok_or_else(|| CompileError::deserialize("invalid function handle index"))?;

            let func_name = module
                .identifiers
                .get(handle.name.0 as usize)
                .ok_or_else(|| CompileError::deserialize("invalid function name index"))?
                .as_str()
                .to_string();

            let params = module
                .signatures
                .get(handle.parameters.0 as usize)
                .ok_or_else(|| CompileError::deserialize("invalid parameters signature index"))?;

            let ret = module
                .signatures
                .get(handle.return_.0 as usize)
                .ok_or_else(|| CompileError::deserialize("invalid return signature index"))?;

            let module_qualified = format!("{address}_{name}");
            let symbol = Mangler::function_symbol(&module_qualified, &func_name);

            functions.push(FunctionInfo {
                name: func_name,
                symbol,
                arg_count: params.0.len(),
                ret_count: ret.0.len(),
                is_public: matches!(def.visibility, Visibility::Public),
                is_native: def.code.is_none(),
                is_generic: !handle.type_parameters.is_empty(),
            });
        }

        Ok(Self {
            address,
            name,
            functions,
        })
    }

    /// Find a function by its Move name.
    pub fn function(&self, name: &str) -> Option<&FunctionInfo> {
        self.functions.iter().find(|f| f.name == name)
    }

    /// Return the sole non-native function, or `None` if there are zero
    /// or more than one.
    pub fn only_function(&self) -> Option<&FunctionInfo> {
        let mut non_native = self.functions.iter().filter(|f| !f.is_native);
        let first = non_native.next()?;
        if non_native.next().is_some() {
            None // ambiguous
        } else {
            Some(first)
        }
    }
}

#[cfg(test)]
mod tests {
    use move_binary_format::file_format::{AbilitySet, Bytecode, SignatureToken};

    use super::ModuleInfo;
    use crate::module::CompiledModuleBuilder;

    #[test]
    fn from_module_basic_metadata() {
        let module = CompiledModuleBuilder::new()
            .function(
                "add",
                vec![SignatureToken::U64, SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::CopyLoc(1),
                    Bytecode::Add,
                    Bytecode::Ret,
                ],
            )
            .build();

        let info = ModuleInfo::from_module(&module).unwrap();
        assert_eq!(info.address, "0x0");
        assert_eq!(info.name, "M");
        assert_eq!(info.functions.len(), 1);

        let f = &info.functions[0];
        assert_eq!(f.name, "add");
        assert_eq!(f.symbol, "_mv_0x0_M_add");
        assert_eq!(f.arg_count, 2);
        assert_eq!(f.ret_count, 1);
        assert!(f.is_public);
        assert!(!f.is_native);
        assert!(!f.is_generic);
    }

    #[test]
    fn function_lookup() {
        let module = CompiledModuleBuilder::new()
            .function(
                "alpha",
                vec![SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![],
                vec![Bytecode::CopyLoc(0), Bytecode::Ret],
            )
            .function(
                "beta",
                vec![SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![],
                vec![Bytecode::CopyLoc(0), Bytecode::Ret],
            )
            .build();

        let info = ModuleInfo::from_module(&module).unwrap();
        assert!(info.function("alpha").is_some());
        assert!(info.function("beta").is_some());
        assert!(info.function("gamma").is_none());
    }

    #[test]
    fn only_function_single() {
        let module = CompiledModuleBuilder::new()
            .function(
                "sole",
                vec![],
                vec![SignatureToken::U64],
                vec![],
                vec![Bytecode::LdU64(0), Bytecode::Ret],
            )
            .build();

        let info = ModuleInfo::from_module(&module).unwrap();
        let f = info.only_function().expect("should find sole function");
        assert_eq!(f.name, "sole");
    }

    #[test]
    fn only_function_multiple_returns_none() {
        let module = CompiledModuleBuilder::new()
            .function(
                "a",
                vec![],
                vec![SignatureToken::U64],
                vec![],
                vec![Bytecode::LdU64(0), Bytecode::Ret],
            )
            .function(
                "b",
                vec![],
                vec![SignatureToken::U64],
                vec![],
                vec![Bytecode::LdU64(1), Bytecode::Ret],
            )
            .build();

        let info = ModuleInfo::from_module(&module).unwrap();
        assert!(info.only_function().is_none(), "ambiguous: two functions");
    }

    #[test]
    fn generic_function_flagged() {
        let module = CompiledModuleBuilder::new()
            .generic_function(
                "identity",
                vec![AbilitySet::EMPTY],
                vec![SignatureToken::TypeParameter(0)],
                vec![SignatureToken::TypeParameter(0)],
                vec![],
                vec![Bytecode::MoveLoc(0), Bytecode::Ret],
            )
            .build();

        let info = ModuleInfo::from_module(&module).unwrap();
        assert_eq!(info.functions.len(), 1);
        assert!(info.functions[0].is_generic);
    }
}
