// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::types::BasicTypeEnum;
use move_model::model::{DatatypeId, ModuleId, RefType, VariantId};
use move_model::ty::Type;
use move_stackless_bytecode::stackless_bytecode::Operation;

use super::state::FunctionState;
use crate::context::DatatypeEnv;
use crate::error::{CompileError, CompileResult, to_field_index};
use crate::layout::EnumLayout;

/// Emits LLVM IR for enum construction and destructuring.
pub(crate) struct EnumEmitter<'a, 'b, 'ctx> {
    state: &'a FunctionState<'b, 'ctx>,
}

impl<'a, 'b, 'ctx> EnumEmitter<'a, 'b, 'ctx> {
    pub(super) fn new(state: &'a FunctionState<'b, 'ctx>) -> Self {
        Self { state }
    }

    pub(super) fn emit(
        &self,
        destinations: &[usize],
        operation: &Operation,
        sources: &[usize],
    ) -> CompileResult<()> {
        match operation {
            Operation::PackVariant(module_id, datatype_id, variant_id, type_args) => self
                .emit_pack_variant(
                    *module_id,
                    *datatype_id,
                    *variant_id,
                    type_args,
                    destinations,
                    sources,
                ),
            Operation::UnpackVariant(module_id, datatype_id, variant_id, type_args, ref_type) => {
                self.emit_unpack_variant(
                    *module_id,
                    *datatype_id,
                    *variant_id,
                    type_args,
                    *ref_type,
                    destinations,
                    sources,
                )
            }
            _ => unreachable!("EnumEmitter::emit called with non-enum op"),
        }
    }

    fn emit_pack_variant(
        &self,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        variant_id: VariantId,
        type_args: &[Type],
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = self.state.ctx;
        let type_args = self.state.instantiate_types(type_args);
        let (layout, enum_type) = self.get_layout_and_type(module_id, datatype_id, &type_args)?;
        let variant = layout.variant(variant_id);
        let payload =
            self.build_payload_struct(&variant.payload_field_types(&type_args), sources)?;
        let tag = self.tag_const(&layout, variant.tag())?;

        let mut enum_value = enum_type.const_zero();
        enum_value = llvm
            .builder
            .build_insert_value(enum_value, tag, 0, "enum_tag")?
            .into_struct_value();
        enum_value = llvm
            .builder
            .build_insert_value(
                enum_value,
                payload,
                variant.payload_field_index()?,
                "enum_payload",
            )?
            .into_struct_value();
        self.state.store(self.state.destination(destinations, 0)?, enum_value.into())?;
        Ok(())
    }

    fn emit_unpack_variant(
        &self,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        variant_id: VariantId,
        type_args: &[Type],
        ref_type: RefType,
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = self.state.ctx;
        let type_args = self.state.instantiate_types(type_args);
        let (layout, enum_type) = self.get_layout_and_type(module_id, datatype_id, &type_args)?;
        let variant = layout.variant(variant_id);
        match ref_type {
            RefType::ByValue => {
                let enum_value = self.state.load_struct(self.state.source(sources, 0)?)?;
                let payload = llvm
                    .builder
                    .build_extract_value(
                        enum_value,
                        variant.payload_field_index()?,
                        "variant_payload",
                    )?
                    .into_struct_value();

                for (i, destination) in destinations.iter().enumerate() {
                    let field = llvm.builder.build_extract_value(
                        payload,
                        to_field_index(i)?,
                        &format!("variant_field_{i}"),
                    )?;
                    self.state.store(*destination, field)?;
                }
            }
            RefType::ByImmRef | RefType::ByMutRef => {
                let enum_ptr = self.state.load_pointer(self.state.source(sources, 0)?)?;
                let payload_ptr = llvm.builder.build_struct_gep(
                    enum_type,
                    enum_ptr,
                    variant.payload_field_index()?,
                    "variant_payload_ptr",
                )?;
                let payload_type = enum_type
                    .get_field_type_at_index(variant.payload_field_index()?)
                    .ok_or_else(|| {
                        CompileError::InvalidReference(format!(
                            "missing payload slot for variant {}",
                            variant.tag()
                        ))
                    })?;
                for (i, destination) in destinations.iter().enumerate() {
                    let field_ptr = llvm.builder.build_struct_gep(
                        payload_type,
                        payload_ptr,
                        to_field_index(i)?,
                        &format!("variant_field_ptr_{i}"),
                    )?;
                    self.state.store(*destination, field_ptr.into())?;
                }
            }
        }
        Ok(())
    }

    fn get_layout_and_type(
        &self,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        type_args: &[Type],
    ) -> CompileResult<(EnumLayout<'b>, inkwell::types::StructType<'ctx>)> {
        let llvm = self.state.ctx;
        let datatype_env = llvm.get_datatype_env(module_id, datatype_id)?;
        let DatatypeEnv::Enum(enum_env) = datatype_env else {
            return Err(CompileError::Unsupported(format!(
                "expected enum datatype for variant op: {:?}",
                Type::Datatype(module_id, datatype_id, type_args.to_vec())
            )));
        };
        let enum_type = self
            .state
            .lower_type(&Type::Datatype(module_id, datatype_id, type_args.to_vec()))?
            .into_struct_type();
        Ok((EnumLayout::new(enum_env), enum_type))
    }

    fn build_payload_struct(
        &self,
        field_types: &[Type],
        sources: &[usize],
    ) -> CompileResult<inkwell::values::StructValue<'ctx>> {
        let llvm = self.state.ctx;
        let payload_types: Vec<BasicTypeEnum<'ctx>> = field_types
            .iter()
            .map(|ty| self.state.lower_type(ty))
            .collect::<Result<_, _>>()?;
        let payload_type = llvm.context.struct_type(&payload_types, false);
        let mut payload = payload_type.get_undef();
        for (i, source) in sources.iter().enumerate() {
            let field = self.state.load_value(*source)?;
            payload = llvm
                .builder
                .build_insert_value(payload, field, to_field_index(i)?, &format!("payload_{i}"))?
                .into_struct_value();
        }
        Ok(payload)
    }

    fn tag_const(
        &self,
        layout: &EnumLayout<'b>,
        tag: usize,
    ) -> CompileResult<inkwell::values::IntValue<'ctx>> {
        let value = tag as u64;
        Ok(match layout.tag_bit_width()? {
            8 => self.state.ctx.i8_type.const_int(value, false),
            16 => self.state.ctx.i16_type.const_int(value, false),
            32 => self.state.ctx.i32_type.const_int(value, false),
            bits => {
                return Err(CompileError::Unsupported(format!(
                    "unsupported enum tag width: {bits}"
                )));
            }
        })
    }
}
