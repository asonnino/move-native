// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::types::IntType;
use move_model::model::{EnumEnv, VariantEnv, VariantId};
use move_model::ty::Type;

use crate::context::LlvmContext;
use crate::error::{CompileError, CompileResult};

pub(crate) struct VariantLayout<'env> {
    env: VariantEnv<'env>,
}

impl<'env> VariantLayout<'env> {
    fn new(env: VariantEnv<'env>) -> Self {
        Self { env }
    }

    pub(crate) fn tag(&self) -> usize {
        self.env.get_tag()
    }

    /// The LLVM struct field index for this variant's payload.
    ///
    /// Field 0 is the tag; payload for variant N is at index N + 1.
    pub(crate) fn payload_field_index(&self) -> CompileResult<u32> {
        u32::try_from(self.env.get_tag() + 1).map_err(|_| {
            CompileError::Unsupported(format!(
                "variant tag {} exceeds u32 range",
                self.env.get_tag()
            ))
        })
    }

    pub(crate) fn payload_field_types(&self, type_args: &[Type]) -> Vec<Type> {
        self.env
            .get_fields()
            .map(|field| {
                let ty = field.get_type();
                if type_args.is_empty() {
                    ty
                } else {
                    ty.instantiate(type_args)
                }
            })
            .collect()
    }
}

/// Compiler-owned layout metadata for a Move enum.
///
/// Enums are represented as a tagged product:
/// `{ tag, variant0_payload, variant1_payload, ... }`
/// where each payload slot is a struct containing the fields for that variant.
pub(crate) struct EnumLayout<'env> {
    env: EnumEnv<'env>,
}

impl<'env> EnumLayout<'env> {
    pub(crate) fn new(env: EnumEnv<'env>) -> Self {
        Self { env }
    }

    pub(crate) fn llvm_name(&self, mangled_args: Option<&str>) -> String {
        let base = self.env.get_full_name_str();
        match mangled_args {
            Some(args) => format!("{base}__{args}"),
            None => base,
        }
    }

    pub(crate) fn tag_bit_width(&self) -> CompileResult<u32> {
        let variants = self.env.get_variant_count();
        if u8::try_from(variants).is_ok() {
            Ok(8)
        } else if u16::try_from(variants).is_ok() {
            Ok(16)
        } else if u32::try_from(variants).is_ok() {
            Ok(32)
        } else {
            Err(CompileError::Unsupported(format!(
                "enum has too many variants: {}",
                self.env.get_full_name_str()
            )))
        }
    }

    /// Return the LLVM integer type for the enum discriminant tag.
    pub(crate) fn tag_int_type<'ctx>(
        &self,
        ctx: &LlvmContext<'ctx>,
    ) -> CompileResult<IntType<'ctx>> {
        match self.tag_bit_width()? {
            8 => Ok(ctx.i8_type),
            16 => Ok(ctx.i16_type),
            32 => Ok(ctx.i32_type),
            bits => Err(CompileError::internal(format!(
                "unexpected tag bit width {bits}"
            ))),
        }
    }

    pub(crate) fn variants(&'env self) -> impl Iterator<Item = VariantLayout<'env>> {
        self.env.get_variants().map(VariantLayout::new)
    }

    pub(crate) fn variant(&'env self, id: VariantId) -> VariantLayout<'env> {
        VariantLayout::new(self.env.get_variant(id))
    }
}

#[cfg(test)]
mod tests {
    use move_model::ty::{PrimitiveType, Type};

    use super::EnumLayout;
    use crate::context::{DatatypeEnv, DatatypeHandle, LlvmContext};
    use crate::module::CompiledModuleBuilder;

    /// Build an `EnumLayout` from a builder module that has exactly one enum.
    fn layout_from_builder(builder: CompiledModuleBuilder) -> impl FnOnce() -> EnumLayout<'static> {
        move || {
            let compiled = builder.build();
            let ctx: &'static LlvmContext<'static> =
                Box::leak(Box::new(LlvmContext::new_from_module(&compiled).unwrap()));
            let module_env = ctx.target_module().unwrap();
            let enum_env = module_env.get_enums().next().expect("module has no enums");
            let handle = DatatypeHandle::new(module_env.get_id(), enum_env.get_id());
            let DatatypeEnv::Enum(e) = ctx.get_datatype_env(handle).unwrap() else {
                panic!("expected enum");
            };
            EnumLayout::new(e)
        }
    }

    #[test]
    fn tag_bit_width_small() {
        let make = layout_from_builder(CompiledModuleBuilder::option());
        let layout = make();
        assert_eq!(layout.tag_bit_width().unwrap(), 8);
    }

    #[test]
    fn variant_count() {
        let make = layout_from_builder(CompiledModuleBuilder::option());
        let layout = make();
        assert_eq!(layout.variants().count(), 2);
    }

    #[test]
    fn variant_tags() {
        let make = layout_from_builder(CompiledModuleBuilder::option());
        let layout = make();
        let tags: Vec<usize> = layout.variants().map(|v| v.tag()).collect();
        assert_eq!(tags, vec![0, 1]);
    }

    #[test]
    fn variant_payload_field_index() {
        let make = layout_from_builder(CompiledModuleBuilder::option());
        let layout = make();
        // Variant 0 (None) → payload at field index 1
        assert_eq!(
            layout
                .variants()
                .next()
                .unwrap()
                .payload_field_index()
                .unwrap(),
            1
        );
        // Variant 1 (Some) → payload at field index 2
        assert_eq!(
            layout
                .variants()
                .nth(1)
                .unwrap()
                .payload_field_index()
                .unwrap(),
            2
        );
    }

    #[test]
    fn variant_payload_field_types_none() {
        let make = layout_from_builder(CompiledModuleBuilder::option());
        let layout = make();
        let none_variant = layout.variants().next().unwrap();
        let fields = none_variant.payload_field_types(&[]);
        assert!(fields.is_empty(), "None variant should have no fields");
    }

    #[test]
    fn variant_payload_field_types_some() {
        let make = layout_from_builder(CompiledModuleBuilder::option());
        let layout = make();
        let some_variant = layout.variants().nth(1).unwrap();
        let fields = some_variant.payload_field_types(&[]);
        assert_eq!(fields.len(), 1);
        assert_eq!(fields[0], Type::Primitive(PrimitiveType::U64));
    }

    #[test]
    fn llvm_name_without_args() {
        let make = layout_from_builder(CompiledModuleBuilder::option());
        let layout = make();
        let name = layout.llvm_name(None);
        assert!(
            name.contains("MyOption"),
            "expected MyOption in name: {name}"
        );
    }

    #[test]
    fn llvm_name_with_args() {
        let make = layout_from_builder(CompiledModuleBuilder::option());
        let layout = make();
        let name = layout.llvm_name(Some("u64"));
        assert!(
            name.contains("MyOption") && name.contains("u64"),
            "expected MyOption__u64 pattern: {name}"
        );
    }
}
