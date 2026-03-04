// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum};
use move_model::ty::{PrimitiveType, Type};

use crate::context::LlvmContext;
use crate::error::{CompileError, CompileResult};

/// Lightweight view for lowering Move types to LLVM types.
///
/// Created on the fly — borrows the LLVM context (which owns the env).
pub(crate) struct TypeLowering<'a, 'ctx> {
    ctx: &'a LlvmContext<'ctx>,
}

impl<'a, 'ctx> TypeLowering<'a, 'ctx> {
    pub fn new(ctx: &'a LlvmContext<'ctx>) -> Self {
        Self { ctx }
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
            Type::Datatype(module_id, datatype_id, type_args) => {
                let struct_env = self
                    .ctx
                    .env()
                    .get_module(*module_id)
                    .into_struct(*datatype_id);
                let name = if type_args.is_empty() {
                    struct_env.get_full_name_str()
                } else {
                    let args = self.ctx.mangle_type_args(type_args)?;
                    format!("{}__{}", struct_env.get_full_name_str(), args)
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
                        let t = if type_args.is_empty() {
                            f.get_type()
                        } else {
                            f.get_type().instantiate(type_args)
                        };
                        self.lower_type(&t)
                    })
                    .collect::<Result<_, _>>()?;
                struct_type.set_body(&field_types, false);
                Ok(struct_type.into())
            }
            other => Err(CompileError::unsupported_type(other.clone())),
        }
    }

    /// Lower Move parameter and return types into an LLVM function type.
    ///
    /// For zero returns -> void, one return -> that type, multiple returns -> anonymous struct.
    pub fn lower_function_type(
        &self,
        parameter_types: &[Type],
        return_types: &[Type],
    ) -> CompileResult<inkwell::types::FunctionType<'ctx>> {
        let params: Vec<BasicMetadataTypeEnum<'ctx>> = parameter_types
            .iter()
            .map(|ty| self.lower_type(ty).map(|t| t.into()))
            .collect::<Result<_, _>>()?;

        Ok(if return_types.is_empty() {
            self.ctx.context.void_type().fn_type(&params, false)
        } else if return_types.len() == 1 {
            let return_type = self.lower_type(&return_types[0])?;
            return_type.fn_type(&params, false)
        } else {
            let llvm_return_types: Vec<BasicTypeEnum<'ctx>> = return_types
                .iter()
                .map(|t| self.lower_type(t))
                .collect::<Result<_, _>>()?;
            let return_struct = self.ctx.context.struct_type(&llvm_return_types, false);
            return_struct.fn_type(&params, false)
        })
    }
}
