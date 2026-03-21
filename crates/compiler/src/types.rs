// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum};
use move_model::ty::{PrimitiveType, Type};

use crate::context::{DatatypeEnv, LlvmContext};
use crate::error::{CompileError, CompileResult};
use crate::layout::EnumLayout;

/// Lightweight view for lowering Move types to LLVM types.
///
/// Created on the fly — borrows the LLVM context (which owns the env).
pub(crate) struct TypeLowering<'a, 'ctx> {
    ctx: &'a LlvmContext<'ctx>,
}

impl<'a, 'ctx> TypeLowering<'a, 'ctx> {
    pub(crate) fn new(ctx: &'a LlvmContext<'ctx>) -> Self {
        Self { ctx }
    }

    /// Lower a `move_model::ty::Type` to an LLVM type.
    pub(crate) fn lower_type(&self, ty: &Type) -> CompileResult<BasicTypeEnum<'ctx>> {
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
                match self.ctx.get_datatype_env(*module_id, *datatype_id)? {
                    DatatypeEnv::Struct(struct_env) => self.lower_struct(struct_env, type_args),
                    DatatypeEnv::Enum(enum_env) => self.lower_enum(enum_env, type_args),
                }
            }
            Type::TypeParameter(idx) => Err(CompileError::UnresolvedTypeParam(*idx)),
            other => Err(CompileError::unsupported(other)),
        }
    }

    /// Lower a Move struct to a named LLVM struct type, with caching.
    fn lower_struct(
        &self,
        struct_env: move_model::model::StructEnv<'_>,
        type_args: &[Type],
    ) -> CompileResult<BasicTypeEnum<'ctx>> {
        let name = if type_args.is_empty() {
            struct_env.get_full_name_str()
        } else {
            let args = self.ctx.mangle_type_args(type_args)?;
            format!("{}__{}", struct_env.get_full_name_str(), args)
        };

        if let Some(existing) = self.ctx.context.get_struct_type(&name) {
            return Ok(existing.into());
        }

        // Create opaque struct first, then set body (handles recursive types).
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

    /// Lower a Move enum to a tagged-union LLVM struct type, with caching.
    fn lower_enum(
        &self,
        enum_env: move_model::model::EnumEnv<'_>,
        type_args: &[Type],
    ) -> CompileResult<BasicTypeEnum<'ctx>> {
        let layout = EnumLayout::new(enum_env);
        let mangled_args = if type_args.is_empty() {
            None
        } else {
            Some(self.ctx.mangle_type_args(type_args)?)
        };
        let name = layout.llvm_name(mangled_args.as_deref());

        if let Some(existing) = self.ctx.context.get_struct_type(&name) {
            return Ok(existing.into());
        }

        let enum_type = self.ctx.context.opaque_struct_type(&name);
        let tag_type = match layout.tag_bit_width()? {
            8 => self.ctx.i8_type.into(),
            16 => self.ctx.i16_type.into(),
            32 => self.ctx.i32_type.into(),
            bits => {
                return Err(CompileError::Unsupported(format!(
                    "unsupported enum tag width: {bits}"
                )));
            }
        };

        let mut storage_fields = vec![tag_type];
        for variant in layout.variants() {
            let payload_types: Vec<BasicTypeEnum<'ctx>> = variant
                .payload_field_types(type_args)
                .into_iter()
                .map(|ty| self.lower_type(&ty))
                .collect::<Result<_, _>>()?;
            storage_fields.push(self.ctx.context.struct_type(&payload_types, false).into());
        }
        enum_type.set_body(&storage_fields, false);
        Ok(enum_type.into())
    }

    /// Lower Move parameter and return types into an LLVM function type.
    ///
    /// For zero returns -> void, one return -> that type, multiple returns -> anonymous struct.
    pub(crate) fn lower_function_type(
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

#[cfg(test)]
mod tests {
    use move_model::ty::{PrimitiveType, Type};

    use super::TypeLowering;
    use crate::context::LlvmContext;
    use crate::module::CompiledModuleBuilder;

    #[test]
    fn primitive_bit_widths() {
        let llvm = LlvmContext::new_for_test();
        let lowering = TypeLowering::new(&llvm);

        let cases = [
            (PrimitiveType::Bool, 8),
            (PrimitiveType::U8, 8),
            (PrimitiveType::U16, 16),
            (PrimitiveType::U32, 32),
            (PrimitiveType::U64, 64),
            (PrimitiveType::U128, 128),
            (PrimitiveType::U256, 256),
            (PrimitiveType::Address, 256),
            (PrimitiveType::Signer, 256),
        ];
        for (p, expected_bits) in cases {
            let ty = lowering.lower_type(&Type::Primitive(p)).unwrap();
            assert_eq!(
                ty.into_int_type().get_bit_width(),
                expected_bits,
                "wrong bit width for {p:?}"
            );
        }
    }

    #[test]
    fn reference_is_pointer() {
        let llvm = LlvmContext::new_for_test();
        let lowering = TypeLowering::new(&llvm);

        let immutable = lowering
            .lower_type(&Type::Reference(
                false,
                Box::new(Type::Primitive(PrimitiveType::U64)),
            ))
            .unwrap();
        let mutable = lowering
            .lower_type(&Type::Reference(
                true,
                Box::new(Type::Primitive(PrimitiveType::U64)),
            ))
            .unwrap();
        assert!(immutable.is_pointer_type());
        assert!(mutable.is_pointer_type());
        assert_eq!(immutable, mutable);
    }

    #[test]
    fn vector_is_pointer() {
        let llvm = LlvmContext::new_for_test();
        let lowering = TypeLowering::new(&llvm);

        let ty = lowering
            .lower_type(&Type::Vector(Box::new(Type::Primitive(PrimitiveType::U8))))
            .unwrap();
        assert!(ty.is_pointer_type());
    }

    #[test]
    fn unsupported_type_is_error() {
        let llvm = LlvmContext::new_for_test();
        let lowering = TypeLowering::new(&llvm);

        assert!(lowering.lower_type(&Type::Error).is_err());
    }

    #[test]
    fn function_type_void_return() {
        let llvm = LlvmContext::new_for_test();
        let lowering = TypeLowering::new(&llvm);

        let function_type = lowering
            .lower_function_type(&[Type::Primitive(PrimitiveType::U64)], &[])
            .unwrap();
        assert_eq!(function_type.count_param_types(), 1);
        assert!(function_type.get_return_type().is_none());
    }

    #[test]
    fn function_type_single_return() {
        let llvm = LlvmContext::new_for_test();
        let lowering = TypeLowering::new(&llvm);

        let function_type = lowering
            .lower_function_type(
                &[Type::Primitive(PrimitiveType::U8)],
                &[Type::Primitive(PrimitiveType::U64)],
            )
            .unwrap();
        assert_eq!(function_type.count_param_types(), 1);
        let ret = function_type
            .get_return_type()
            .expect("should have a return type");
        assert_eq!(ret.into_int_type().get_bit_width(), 64);
    }

    #[test]
    fn function_type_multiple_returns() {
        let llvm = LlvmContext::new_for_test();
        let lowering = TypeLowering::new(&llvm);

        let function_type = lowering
            .lower_function_type(
                &[],
                &[
                    Type::Primitive(PrimitiveType::U8),
                    Type::Primitive(PrimitiveType::U64),
                ],
            )
            .unwrap();
        let ret = function_type
            .get_return_type()
            .expect("should have a return type");
        let struct_ty = ret.into_struct_type();
        assert_eq!(struct_ty.count_fields(), 2);
    }

    #[test]
    fn lower_enum_type() {
        let compiled = CompiledModuleBuilder::option().build();
        let ctx = LlvmContext::new_from_module(&compiled).unwrap();
        let module_env = ctx.target_module().unwrap();
        let enum_env = module_env.get_enums().next().expect("no enums");
        let module_id = module_env.get_id();
        let datatype_id = enum_env.get_id();

        let lowering = TypeLowering::new(&ctx);
        let ty = lowering
            .lower_type(&Type::Datatype(module_id, datatype_id, vec![]))
            .unwrap();

        let struct_ty = ty.into_struct_type();
        // 1 tag field + 2 variant payload slots = 3 fields
        assert_eq!(
            struct_ty.count_fields(),
            3,
            "expected 3 fields (tag + 2 variant payloads)"
        );
        // Tag field is i8 (≤256 variants)
        assert_eq!(
            struct_ty
                .get_field_type_at_index(0)
                .unwrap()
                .into_int_type()
                .get_bit_width(),
            8,
            "tag should be i8"
        );
    }
}
