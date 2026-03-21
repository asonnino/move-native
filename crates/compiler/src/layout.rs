// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use move_model::model::{EnumEnv, VariantEnv, VariantId};
use move_model::ty::Type;

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

    pub(crate) fn variants(&'env self) -> impl Iterator<Item = VariantLayout<'env>> {
        self.env.get_variants().map(VariantLayout::new)
    }

    pub(crate) fn variant(&'env self, id: VariantId) -> VariantLayout<'env> {
        VariantLayout::new(self.env.get_variant(id))
    }
}
