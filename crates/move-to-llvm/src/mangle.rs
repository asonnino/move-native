// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use move_model::model::{FunctionEnv, GlobalEnv};
use move_model::ty::{PrimitiveType, Type};

use crate::error::{CompileError, CompileResult};

/// Name mangling for Move types and native symbols.
pub(crate) struct Mangler<'a> {
    env: &'a GlobalEnv,
}

impl<'a> Mangler<'a> {
    pub(crate) fn new(env: &'a GlobalEnv) -> Self {
        Self { env }
    }

    /// Mangle a Move type into a deterministic, symbol-safe string.
    pub(crate) fn mangle_type(&self, ty: &Type) -> CompileResult<String> {
        match ty {
            Type::Primitive(PrimitiveType::Bool) => Ok("bool".to_string()),
            Type::Primitive(PrimitiveType::U8) => Ok("u8".to_string()),
            Type::Primitive(PrimitiveType::U16) => Ok("u16".to_string()),
            Type::Primitive(PrimitiveType::U32) => Ok("u32".to_string()),
            Type::Primitive(PrimitiveType::U64) => Ok("u64".to_string()),
            Type::Primitive(PrimitiveType::U128) => Ok("u128".to_string()),
            Type::Primitive(PrimitiveType::U256) => Ok("u256".to_string()),
            Type::Primitive(PrimitiveType::Address) => Ok("address".to_string()),
            Type::Primitive(PrimitiveType::Signer) => Ok("signer".to_string()),
            Type::Vector(inner) => Ok(format!("vec${}", self.mangle_type(inner)?)),
            Type::Datatype(module_id, datatype_id, type_args) => {
                let struct_env = self.env.get_module(*module_id).into_struct(*datatype_id);
                let base = struct_env.get_full_name_str().replace("::", "_");
                if type_args.is_empty() {
                    Ok(base)
                } else {
                    let args = self.mangle_type_args(type_args)?;
                    Ok(format!("{base}${args}"))
                }
            }
            Type::Reference(false, inner) => Ok(format!("ref${}", self.mangle_type(inner)?)),
            Type::Reference(true, inner) => Ok(format!("mut${}", self.mangle_type(inner)?)),
            Type::TypeParameter(idx) => Ok(format!("T{idx}")),
            other => Err(CompileError::unsupported_type(other.clone())),
        }
    }

    /// Mangle a slice of type arguments into a `$`-separated string.
    pub(crate) fn mangle_type_args(&self, type_args: &[Type]) -> CompileResult<String> {
        Ok(type_args
            .iter()
            .map(|t| self.mangle_type(t))
            .collect::<Result<Vec<_>, _>>()?
            .join("$"))
    }

    /// Build the extern symbol name for a native function call with concrete type args.
    ///
    /// Format: `__move_rt_<addr>_<module>_<function>$<type_args>`
    pub(crate) fn mangle_native_symbol(
        &self,
        callee_env: &FunctionEnv<'_>,
        type_args: &[Type],
    ) -> CompileResult<String> {
        let module_env = &callee_env.module_env;
        let address = module_env.get_name().addr().to_str_radix(16);
        let module_name = module_env
            .get_name()
            .name()
            .display(self.env.symbol_pool())
            .to_string();
        let function_name = callee_env.get_name_str();

        let base = format!("__move_rt_0x{address}_{module_name}_{function_name}");
        if type_args.is_empty() {
            Ok(base)
        } else {
            let args = self.mangle_type_args(type_args)?;
            Ok(format!("{base}${args}"))
        }
    }
}
