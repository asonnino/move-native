// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use move_model::model::DatatypeId;
use move_model::model::ModuleId;
use move_model::ty::Type;
use move_stackless_bytecode::stackless_bytecode::Operation;

use super::state::FunctionState;
use crate::error::CompileResult;

/// Emits LLVM IR for struct and reference operations
/// (Pack, Unpack, BorrowLoc, BorrowField, GetField, ReadRef, WriteRef,
/// FreezeRef, Destroy).
pub(crate) struct StructEmitter<'a, 'b, 'ctx> {
    state: &'a FunctionState<'b, 'ctx>,
}

impl<'a, 'b, 'ctx> StructEmitter<'a, 'b, 'ctx> {
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
            Operation::Pack(module_id, datatype_id, type_args) => {
                self.emit_pack(*module_id, *datatype_id, type_args, destinations, sources)
            }
            Operation::Unpack(module_id, datatype_id, _type_args) => {
                self.emit_unpack(*module_id, *datatype_id, destinations, sources)
            }
            Operation::BorrowLoc => self.emit_borrow_loc(destinations, sources),
            Operation::BorrowField(module_id, datatype_id, type_args, offset) => self
                .emit_borrow_field(
                    *module_id,
                    *datatype_id,
                    type_args,
                    *offset,
                    destinations,
                    sources,
                ),
            Operation::GetField(_module_id, _datatype_id, _type_args, offset) => {
                self.emit_get_field(*offset, destinations, sources)
            }
            Operation::ReadRef => self.emit_read_ref(destinations, sources),
            Operation::WriteRef => self.emit_write_ref(sources),
            Operation::FreezeRef => self.emit_freeze_ref(destinations, sources),
            Operation::Destroy => Ok(()),
            _ => unreachable!("StructEmitter::emit called with non-struct op"),
        }
    }

    fn emit_pack(
        &self,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        type_args: &[Type],
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = self.state.ctx;
        let type_args = self.state.instantiate_types(type_args);
        let struct_ty = self
            .state
            .lower_type(&Type::Datatype(module_id, datatype_id, type_args))?
            .into_struct_type();
        let mut agg = struct_ty.get_undef();
        for (i, source) in sources.iter().enumerate() {
            let field_val = self.state.load_value(*source)?;
            agg = llvm
                .builder
                .build_insert_value(agg, field_val, i as u32, &format!("pack_{i}"))?
                .into_struct_value();
        }
        self.state.store(destinations[0], agg.into())?;
        Ok(())
    }

    fn emit_unpack(
        &self,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = self.state.ctx;
        let struct_val = self.state.load_value(sources[0])?.into_struct_value();
        let struct_env = self.state.ctx.get_struct_env(module_id, datatype_id);
        let field_count = struct_env.get_fields().count();
        for (i, destination) in destinations.iter().enumerate().take(field_count) {
            let field_val =
                llvm.builder
                    .build_extract_value(struct_val, i as u32, &format!("unpack_{i}"))?;
            self.state.store(*destination, field_val)?;
        }
        Ok(())
    }

    fn emit_borrow_loc(&self, destinations: &[usize], sources: &[usize]) -> CompileResult<()> {
        let ptr = self.state.locals[sources[0]].alloca;
        self.state.store(destinations[0], ptr.into())?;
        Ok(())
    }

    fn emit_borrow_field(
        &self,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        type_args: &[Type],
        offset: usize,
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = self.state.ctx;
        let struct_ptr = self.state.load_value(sources[0])?.into_pointer_value();
        let type_args = self.state.instantiate_types(type_args);
        let struct_ty =
            self.state
                .lower_type(&Type::Datatype(module_id, datatype_id, type_args))?;
        let field_ptr =
            llvm.builder
                .build_struct_gep(struct_ty, struct_ptr, offset as u32, "borrow_field")?;
        self.state.store(destinations[0], field_ptr.into())?;
        Ok(())
    }

    fn emit_get_field(
        &self,
        offset: usize,
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = self.state.ctx;
        let struct_val = self.state.load_value(sources[0])?.into_struct_value();
        let field_val = llvm
            .builder
            .build_extract_value(struct_val, offset as u32, "getfield")?;
        self.state.store(destinations[0], field_val)?;
        Ok(())
    }

    fn emit_read_ref(&self, destinations: &[usize], sources: &[usize]) -> CompileResult<()> {
        let llvm = self.state.ctx;
        let ptr = self.state.load_value(sources[0])?.into_pointer_value();
        let pointee_ty = self.state.pointee_type(sources[0])?;
        let val = llvm.builder.build_load(pointee_ty, ptr, "read_ref")?;
        self.state.store(destinations[0], val)?;
        Ok(())
    }

    fn emit_write_ref(&self, sources: &[usize]) -> CompileResult<()> {
        let llvm = self.state.ctx;
        let ptr = self.state.load_value(sources[0])?.into_pointer_value();
        let val = self.state.load_value(sources[1])?;
        llvm.builder.build_store(ptr, val)?;
        Ok(())
    }

    fn emit_freeze_ref(&self, destinations: &[usize], sources: &[usize]) -> CompileResult<()> {
        let ptr = self.state.load_value(sources[0])?;
        self.state.store(destinations[0], ptr)?;
        Ok(())
    }
}
