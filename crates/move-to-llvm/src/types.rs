// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::types::IntType;
use move_model::ty::{PrimitiveType, Type};

use crate::context::LlvmContext;
use crate::error::CompileError;

/// Lower a `move_model::ty::Type` to an LLVM integer type.
pub fn lower_model_type<'ctx>(
    ctx: &LlvmContext<'ctx>,
    ty: &Type,
) -> Result<IntType<'ctx>, CompileError> {
    match ty {
        Type::Primitive(PrimitiveType::U8) => Ok(ctx.i8_type),
        Type::Primitive(PrimitiveType::U16) => Ok(ctx.i16_type),
        Type::Primitive(PrimitiveType::U32) => Ok(ctx.i32_type),
        Type::Primitive(PrimitiveType::U64) => Ok(ctx.i64_type),
        Type::Primitive(PrimitiveType::U128) => Ok(ctx.i128_type),
        Type::Primitive(PrimitiveType::U256) => Ok(ctx.i256_type),
        Type::Primitive(PrimitiveType::Bool) => Ok(ctx.i8_type),
        other => Err(CompileError::UnsupportedType(format!("{:?}", other))),
    }
}
