// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Deterministic type mangling for symbol names.
//!
//! Produces unique, assembly-safe strings from Move types so that
//! monomorphized native function externs get distinct symbol names
//! (e.g. `__move_rt_0x1_vector_push_back$u64`).

use move_model::model::{FunctionEnv, GlobalEnv};
use move_model::ty::{PrimitiveType, Type};

/// Mangle a Move type into a deterministic, symbol-safe string.
pub fn mangle_type(env: &GlobalEnv, ty: &Type) -> String {
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
        Type::Vector(inner) => format!("vec${}", mangle_type(env, inner)),
        Type::Datatype(mid, did, type_args) => {
            let struct_env = env.get_module(*mid).into_struct(*did);
            let base = struct_env.get_full_name_str().replace("::", "_");
            if type_args.is_empty() {
                base
            } else {
                let args = mangle_type_args(env, type_args);
                format!("{base}${args}")
            }
        }
        Type::Reference(false, inner) => format!("ref${}", mangle_type(env, inner)),
        Type::Reference(true, inner) => format!("mut${}", mangle_type(env, inner)),
        Type::TypeParameter(idx) => format!("T{idx}"),
        other => format!("{other:?}"),
    }
}

/// Mangle a slice of type arguments into a `$`-separated string.
pub fn mangle_type_args(env: &GlobalEnv, type_args: &[Type]) -> String {
    type_args
        .iter()
        .map(|t| mangle_type(env, t))
        .collect::<Vec<_>>()
        .join("$")
}

/// Build the extern symbol name for a native function call with concrete type args.
///
/// Format: `__move_rt_<addr>_<module>_<function>$<type_args>`
///
/// Example: `__move_rt_0x1_vector_push_back$u64`
pub fn mangle_native_symbol(
    env: &GlobalEnv,
    callee_env: &FunctionEnv<'_>,
    type_args: &[Type],
) -> String {
    let addr = callee_env.module_env.get_name().addr().to_str_radix(16);
    let module_name = callee_env
        .module_env
        .get_name()
        .name()
        .display(env.symbol_pool())
        .to_string();
    let func_name = callee_env.get_name_str();

    let base = format!("__move_rt_0x{addr}_{module_name}_{func_name}");
    if type_args.is_empty() {
        base
    } else {
        let args = mangle_type_args(env, type_args);
        format!("{base}${args}")
    }
}
