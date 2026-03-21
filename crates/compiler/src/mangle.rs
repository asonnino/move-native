// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use move_model::model::{FunctionEnv, GlobalEnv};
use move_model::ty::{PrimitiveType, Type};

use crate::error::{CompileError, CompileResult};
use crate::layout::EnumLayout;

/// Name mangling for Move types and native symbols.
pub(crate) struct Mangler<'a> {
    env: &'a GlobalEnv,
}

impl<'a> Mangler<'a> {
    pub(crate) fn new(env: &'a GlobalEnv) -> Self {
        Self { env }
    }

    /// Create a `Mangler` backed by an empty `GlobalEnv` for unit testing.
    ///
    /// The leaked env is never accessed for primitive, vector, reference, or
    /// type-parameter branches.
    #[cfg(test)]
    fn new_for_test() -> Mangler<'static> {
        let env = Box::leak(Box::new(GlobalEnv::new()));
        Mangler::new(env)
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
                let base = self.mangle_datatype_base(*module_id, *datatype_id)?;
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
            other => Err(CompileError::unsupported(other)),
        }
    }

    /// Resolve the base mangled name for a struct or enum datatype.
    fn mangle_datatype_base(
        &self,
        module_id: move_model::model::ModuleId,
        datatype_id: move_model::model::DatatypeId,
    ) -> CompileResult<String> {
        let module_env = self.env.get_module(module_id);
        let symbol = datatype_id.symbol();
        if let Some(struct_env) = module_env.find_struct(symbol) {
            Ok(struct_env.get_full_name_str().replace("::", "_"))
        } else if let Some(enum_env) = module_env.find_enum(symbol) {
            Ok(EnumLayout::new(enum_env).llvm_name(None).replace("::", "_"))
        } else {
            Err(CompileError::internal(format!(
                "undefined datatype {symbol:?} in module {}",
                module_env.get_full_name_str()
            )))
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

#[cfg(test)]
mod tests {
    use move_model::ty::{PrimitiveType, Type};

    use super::Mangler;

    #[test]
    fn primitives() {
        let m = Mangler::new_for_test();
        let cases = [
            (PrimitiveType::Bool, "bool"),
            (PrimitiveType::U8, "u8"),
            (PrimitiveType::U16, "u16"),
            (PrimitiveType::U32, "u32"),
            (PrimitiveType::U64, "u64"),
            (PrimitiveType::U128, "u128"),
            (PrimitiveType::U256, "u256"),
            (PrimitiveType::Address, "address"),
            (PrimitiveType::Signer, "signer"),
        ];
        for (p, expected) in cases {
            assert_eq!(m.mangle_type(&Type::Primitive(p)).unwrap(), expected);
        }
    }

    #[test]
    fn vector_of_primitive() {
        let m = Mangler::new_for_test();
        let ty = Type::Vector(Box::new(Type::Primitive(PrimitiveType::U64)));
        assert_eq!(m.mangle_type(&ty).unwrap(), "vec$u64");
    }

    #[test]
    fn nested_vector() {
        let m = Mangler::new_for_test();
        let inner = Type::Vector(Box::new(Type::Primitive(PrimitiveType::U8)));
        let ty = Type::Vector(Box::new(inner));
        assert_eq!(m.mangle_type(&ty).unwrap(), "vec$vec$u8");
    }

    #[test]
    fn immutable_reference() {
        let m = Mangler::new_for_test();
        let ty = Type::Reference(false, Box::new(Type::Primitive(PrimitiveType::U64)));
        assert_eq!(m.mangle_type(&ty).unwrap(), "ref$u64");
    }

    #[test]
    fn mutable_reference() {
        let m = Mangler::new_for_test();
        let ty = Type::Reference(true, Box::new(Type::Primitive(PrimitiveType::U64)));
        assert_eq!(m.mangle_type(&ty).unwrap(), "mut$u64");
    }

    #[test]
    fn type_parameter() {
        let m = Mangler::new_for_test();
        assert_eq!(m.mangle_type(&Type::TypeParameter(0)).unwrap(), "T0");
        assert_eq!(m.mangle_type(&Type::TypeParameter(3)).unwrap(), "T3");
    }

    #[test]
    fn unsupported_type_is_error() {
        let m = Mangler::new_for_test();
        assert!(m.mangle_type(&Type::Error).is_err());
    }

    #[test]
    fn mangle_type_args_multiple() {
        let m = Mangler::new_for_test();
        let args = vec![
            Type::Primitive(PrimitiveType::U8),
            Type::Primitive(PrimitiveType::U64),
            Type::Primitive(PrimitiveType::Bool),
        ];
        assert_eq!(m.mangle_type_args(&args).unwrap(), "u8$u64$bool");
    }

    #[test]
    fn mangle_type_args_empty() {
        let m = Mangler::new_for_test();
        assert_eq!(m.mangle_type_args(&[]).unwrap(), "");
    }

    #[test]
    fn ref_to_vector() {
        let m = Mangler::new_for_test();
        let ty = Type::Reference(
            false,
            Box::new(Type::Vector(Box::new(Type::Primitive(PrimitiveType::U8)))),
        );
        assert_eq!(m.mangle_type(&ty).unwrap(), "ref$vec$u8");
    }
}
