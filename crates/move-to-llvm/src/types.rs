// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::types::BasicTypeEnum;
use move_model::model::GlobalEnv;
use move_model::ty::{PrimitiveType, Type};

use crate::context::LlvmContext;
use crate::error::CompileError;

/// Lower a `move_model::ty::Type` to an LLVM type.
pub fn lower_model_type<'ctx>(
    ctx: &LlvmContext<'ctx>,
    env: &GlobalEnv,
    ty: &Type,
) -> Result<BasicTypeEnum<'ctx>, CompileError> {
    match ty {
        Type::Primitive(PrimitiveType::U8) => Ok(ctx.i8_type.into()),
        Type::Primitive(PrimitiveType::U16) => Ok(ctx.i16_type.into()),
        Type::Primitive(PrimitiveType::U32) => Ok(ctx.i32_type.into()),
        Type::Primitive(PrimitiveType::U64) => Ok(ctx.i64_type.into()),
        Type::Primitive(PrimitiveType::U128) => Ok(ctx.i128_type.into()),
        Type::Primitive(PrimitiveType::U256) => Ok(ctx.i256_type.into()),
        Type::Primitive(PrimitiveType::Bool) => Ok(ctx.i8_type.into()),
        Type::Reference(_, _) => Ok(ctx.ptr_type.into()),
        Type::Datatype(mid, did, type_args) => {
            if !type_args.is_empty() {
                return Err(CompileError::UnsupportedType(
                    "generic structs not yet supported".to_string(),
                ));
            }
            let struct_env = env.get_module(*mid).into_struct(*did);
            let name = struct_env.get_full_name_str();

            // Return cached struct type if already created
            if let Some(existing) = ctx.context.get_struct_type(&name) {
                return Ok(existing.into());
            }

            // Create opaque struct, then set body (handles recursive types)
            let struct_type = ctx.context.opaque_struct_type(&name);
            let field_types: Vec<BasicTypeEnum<'ctx>> = struct_env
                .get_fields()
                .map(|f| lower_model_type(ctx, env, &f.get_type()))
                .collect::<Result<_, _>>()?;
            struct_type.set_body(&field_types, false);
            Ok(struct_type.into())
        }
        other => Err(CompileError::UnsupportedType(format!("{:?}", other))),
    }
}
