// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum};
use move_model::ty::{PrimitiveType, Type};

use crate::context::LlvmContext;
use crate::error::{CompileError, CompileResult};
use crate::mangle::Mangler;

/// Lightweight view for lowering Move types to LLVM types.
///
/// Created on the fly via `Compiler::types()` — borrows the LLVM context
/// and mangler without owning them.
pub(crate) struct TypeLowering<'a, 'ctx> {
    ctx: &'a LlvmContext<'ctx>,
    mangler: &'a Mangler,
}

impl<'a, 'ctx> TypeLowering<'a, 'ctx> {
    pub fn new(ctx: &'a LlvmContext<'ctx>, mangler: &'a Mangler) -> Self {
        Self { ctx, mangler }
    }

    /// Lower a `move_model::ty::Type` to an LLVM type.
    pub fn lower_type(&self, ty: &Type) -> CompileResult<BasicTypeEnum<'ctx>> {
        match ty {
            Type::Primitive(PrimitiveType::U8) => Ok(self.ctx.i8_type.into()),
            Type::Primitive(PrimitiveType::U16) => Ok(self.ctx.i16_type.into()),
            Type::Primitive(PrimitiveType::U32) => Ok(self.ctx.i32_type.into()),
            Type::Primitive(PrimitiveType::U64) => Ok(self.ctx.i64_type.into()),
            Type::Primitive(PrimitiveType::U128) => Ok(self.ctx.i128_type.into()),
            Type::Primitive(PrimitiveType::U256) => Ok(self.ctx.i256_type.into()),
            Type::Primitive(PrimitiveType::Bool) => Ok(self.ctx.i8_type.into()),
            Type::Primitive(PrimitiveType::Address) => Ok(self.ctx.i256_type.into()),
            Type::Primitive(PrimitiveType::Signer) => Ok(self.ctx.i256_type.into()),
            Type::Reference(_, _) => Ok(self.ctx.ptr_type.into()),
            Type::Vector(_) => Ok(self.ctx.ptr_type.into()),
            Type::Datatype(mid, did, type_args) => {
                let struct_env = self.mangler.env().get_module(*mid).into_struct(*did);
                let name = if type_args.is_empty() {
                    struct_env.get_full_name_str()
                } else {
                    format!(
                        "{}__{}",
                        struct_env.get_full_name_str(),
                        self.mangler.mangle_type_args(type_args)
                    )
                };

                // Return cached struct type if already created
                if let Some(existing) = self.ctx.context.get_struct_type(&name) {
                    return Ok(existing.into());
                }

                // Create opaque struct, then set body (handles recursive types)
                let struct_type = self.ctx.context.opaque_struct_type(&name);
                let field_types: Vec<BasicTypeEnum<'ctx>> = struct_env
                    .get_fields()
                    .map(|f| {
                        let ft = if type_args.is_empty() {
                            f.get_type()
                        } else {
                            f.get_type().instantiate(type_args)
                        };
                        self.lower_type(&ft)
                    })
                    .collect::<Result<_, _>>()?;
                struct_type.set_body(&field_types, false);
                Ok(struct_type.into())
            }
            other => Err(CompileError::UnsupportedType(format!("{:?}", other))),
        }
    }

    /// Build an LLVM function type from Move return types and LLVM param types.
    ///
    /// For zero returns -> void, one return -> that type, multiple returns -> anonymous struct.
    pub fn build_fn_type(
        &self,
        ret_types: &[Type],
        param_types: &[BasicMetadataTypeEnum<'ctx>],
    ) -> CompileResult<inkwell::types::FunctionType<'ctx>> {
        Ok(if ret_types.is_empty() {
            self.ctx.context.void_type().fn_type(param_types, false)
        } else if ret_types.len() == 1 {
            let ret = self.lower_type(&ret_types[0])?;
            ret.fn_type(param_types, false)
        } else {
            let llvm_ret_types: Vec<BasicTypeEnum<'ctx>> = ret_types
                .iter()
                .map(|t| self.lower_type(t))
                .collect::<Result<_, _>>()?;
            let ret_struct = self.ctx.context.struct_type(&llvm_ret_types, false);
            ret_struct.fn_type(param_types, false)
        })
    }
}
