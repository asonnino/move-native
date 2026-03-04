// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use move_binary_format::CompiledModule;
use move_model::model::{FunctionEnv, GlobalEnv, ModuleEnv};
use move_model::ty::{PrimitiveType, Type};

use crate::error::{CompileError, CompileResult};

/// Name mangling for Move types and native symbols.
///
/// Owns the `GlobalEnv` so that mangling and environment access are
/// colocated — callers reach the env via `Mangler::env()`.
pub(crate) struct Mangler {
    env: GlobalEnv,
}

impl Mangler {
    /// Build a `GlobalEnv` from the target module and its dependencies,
    /// then wrap it in a `Mangler`.
    pub fn new(module: &CompiledModule, deps: &[CompiledModule]) -> CompileResult<Self> {
        let all_modules: Vec<&CompiledModule> =
            deps.iter().chain(std::iter::once(module)).collect();
        let env = move_model::run_bytecode_model_builder(all_modules)
            .map_err(|e| CompileError::ModelBuilder(e.to_string()))?;
        Ok(Self { env })
    }

    pub fn env(&self) -> &GlobalEnv {
        &self.env
    }

    /// The module being compiled (always the last one added to the environment).
    pub fn target_module(&self) -> ModuleEnv<'_> {
        self.env.get_modules().last().unwrap()
    }

    /// Mangle a Move type into a deterministic, symbol-safe string.
    pub fn mangle_type(&self, ty: &Type) -> String {
        match ty {
            Type::Primitive(PrimitiveType::Bool) => "bool".to_string(),
            Type::Primitive(PrimitiveType::U8) => "u8".to_string(),
            Type::Primitive(PrimitiveType::U16) => "u16".to_string(),
            Type::Primitive(PrimitiveType::U32) => "u32".to_string(),
            Type::Primitive(PrimitiveType::U64) => "u64".to_string(),
            Type::Primitive(PrimitiveType::U128) => "u128".to_string(),
            Type::Primitive(PrimitiveType::U256) => "u256".to_string(),
            Type::Primitive(PrimitiveType::Address) => "address".to_string(),
            Type::Primitive(PrimitiveType::Signer) => "signer".to_string(),
            Type::Vector(inner) => format!("vec${}", self.mangle_type(inner)),
            Type::Datatype(mid, did, type_args) => {
                let struct_env = self.env.get_module(*mid).into_struct(*did);
                let base = struct_env.get_full_name_str().replace("::", "_");
                if type_args.is_empty() {
                    base
                } else {
                    let args = self.mangle_type_args(type_args);
                    format!("{base}${args}")
                }
            }
            Type::Reference(false, inner) => format!("ref${}", self.mangle_type(inner)),
            Type::Reference(true, inner) => format!("mut${}", self.mangle_type(inner)),
            Type::TypeParameter(idx) => format!("T{idx}"),
            other => format!("{other:?}"),
        }
    }

    /// Mangle a slice of type arguments into a `$`-separated string.
    pub fn mangle_type_args(&self, type_args: &[Type]) -> String {
        type_args
            .iter()
            .map(|t| self.mangle_type(t))
            .collect::<Vec<_>>()
            .join("$")
    }

    /// Build the extern symbol name for a native function call with concrete type args.
    ///
    /// Format: `__move_rt_<addr>_<module>_<function>$<type_args>`
    pub fn mangle_native_symbol(&self, callee_env: &FunctionEnv<'_>, type_args: &[Type]) -> String {
        let addr = callee_env.module_env.get_name().addr().to_str_radix(16);
        let module_name = callee_env
            .module_env
            .get_name()
            .name()
            .display(self.env.symbol_pool())
            .to_string();
        let func_name = callee_env.get_name_str();

        let base = format!("__move_rt_0x{addr}_{module_name}_{func_name}");
        if type_args.is_empty() {
            base
        } else {
            let args = self.mangle_type_args(type_args);
            format!("{base}${args}")
        }
    }
}
