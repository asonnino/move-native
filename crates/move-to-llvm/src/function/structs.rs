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
    pub fn new(state: &'a FunctionState<'b, 'ctx>) -> Self {
        Self { state }
    }

    pub fn emit(&self, dsts: &[usize], op: &Operation, srcs: &[usize]) -> CompileResult<()> {
        match op {
            Operation::Pack(mid, did, type_args) => {
                self.emit_pack(*mid, *did, type_args, dsts, srcs)
            }
            Operation::Unpack(mid, did, _type_args) => self.emit_unpack(*mid, *did, dsts, srcs),
            Operation::BorrowLoc => self.emit_borrow_loc(dsts, srcs),
            Operation::BorrowField(mid, did, type_args, offset) => {
                self.emit_borrow_field(*mid, *did, type_args, *offset, dsts, srcs)
            }
            Operation::GetField(_mid, _did, _type_args, offset) => {
                self.emit_get_field(*offset, dsts, srcs)
            }
            Operation::ReadRef => self.emit_read_ref(dsts, srcs),
            Operation::WriteRef => self.emit_write_ref(srcs),
            Operation::FreezeRef => self.emit_freeze_ref(dsts, srcs),
            Operation::Destroy => Ok(()),
            _ => unreachable!("StructEmitter::emit called with non-struct op"),
        }
    }

    fn emit_pack(
        &self,
        mid: ModuleId,
        did: DatatypeId,
        type_args: &[Type],
        dsts: &[usize],
        srcs: &[usize],
    ) -> CompileResult<()> {
        let llvm = self.state.ctx;
        let type_args = self.state.inst_types(type_args);
        let struct_ty = self
            .state
            .lower_type(&Type::Datatype(mid, did, type_args))?
            .into_struct_type();
        let mut agg = struct_ty.get_undef();
        for (i, src) in srcs.iter().enumerate() {
            let field_val = self.state.load_value(*src)?;
            agg = llvm
                .builder
                .build_insert_value(agg, field_val, i as u32, &format!("pack_{i}"))
                .unwrap()
                .into_struct_value();
        }
        self.state.store(dsts[0], agg.into());
        Ok(())
    }

    fn emit_unpack(
        &self,
        mid: ModuleId,
        did: DatatypeId,
        dsts: &[usize],
        srcs: &[usize],
    ) -> CompileResult<()> {
        let llvm = self.state.ctx;
        let struct_val = self.state.load_value(srcs[0])?.into_struct_value();
        let struct_env = self.state.ctx.env().get_module(mid).into_struct(did);
        let field_count = struct_env.get_fields().count();
        for (i, dst) in dsts.iter().enumerate().take(field_count) {
            let field_val = llvm
                .builder
                .build_extract_value(struct_val, i as u32, &format!("unpack_{i}"))
                .unwrap();
            self.state.store(*dst, field_val);
        }
        Ok(())
    }

    fn emit_borrow_loc(&self, dsts: &[usize], srcs: &[usize]) -> CompileResult<()> {
        let ptr = self.state.locals.borrow()[srcs[0]].alloca;
        self.state.store(dsts[0], ptr.into());
        Ok(())
    }

    fn emit_borrow_field(
        &self,
        mid: ModuleId,
        did: DatatypeId,
        type_args: &[Type],
        offset: usize,
        dsts: &[usize],
        srcs: &[usize],
    ) -> CompileResult<()> {
        let llvm = self.state.ctx;
        let struct_ptr = self.state.load_value(srcs[0])?.into_pointer_value();
        let type_args = self.state.inst_types(type_args);
        let struct_ty = self
            .state
            .lower_type(&Type::Datatype(mid, did, type_args))?;
        let field_ptr = llvm
            .builder
            .build_struct_gep(struct_ty, struct_ptr, offset as u32, "borrow_field")
            .unwrap();
        self.state.store(dsts[0], field_ptr.into());
        Ok(())
    }

    fn emit_get_field(&self, offset: usize, dsts: &[usize], srcs: &[usize]) -> CompileResult<()> {
        let llvm = self.state.ctx;
        let struct_val = self.state.load_value(srcs[0])?.into_struct_value();
        let field_val = llvm
            .builder
            .build_extract_value(struct_val, offset as u32, "getfield")
            .unwrap();
        self.state.store(dsts[0], field_val);
        Ok(())
    }

    fn emit_read_ref(&self, dsts: &[usize], srcs: &[usize]) -> CompileResult<()> {
        let llvm = self.state.ctx;
        let ptr = self.state.load_value(srcs[0])?.into_pointer_value();
        let pointee_ty = self.state.pointee_type(srcs[0])?;
        let val = llvm
            .builder
            .build_load(pointee_ty, ptr, "read_ref")
            .unwrap();
        self.state.store(dsts[0], val);
        Ok(())
    }

    fn emit_write_ref(&self, srcs: &[usize]) -> CompileResult<()> {
        let llvm = self.state.ctx;
        let ptr = self.state.load_value(srcs[0])?.into_pointer_value();
        let val = self.state.load_value(srcs[1])?;
        llvm.builder.build_store(ptr, val).unwrap();
        Ok(())
    }

    fn emit_freeze_ref(&self, dsts: &[usize], srcs: &[usize]) -> CompileResult<()> {
        let ptr = self.state.load_value(srcs[0])?;
        self.state.store(dsts[0], ptr);
        Ok(())
    }
}
