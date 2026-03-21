// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use move_model::ty::Type;
use move_stackless_bytecode::stackless_bytecode::Operation;

use super::state::FunctionState;
use crate::context::DatatypeHandle;
use crate::error::{CompileResult, to_field_index};

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
                let handle = DatatypeHandle::new(*module_id, *datatype_id);
                self.emit_pack(handle, type_args, destinations, sources)
            }
            Operation::Unpack(module_id, datatype_id, type_args) => {
                let handle = DatatypeHandle::new(*module_id, *datatype_id);
                self.emit_unpack(handle, type_args, destinations, sources)
            }
            Operation::BorrowLoc => self.emit_borrow_loc(destinations, sources),
            Operation::BorrowField(module_id, datatype_id, type_args, offset) => {
                let handle = DatatypeHandle::new(*module_id, *datatype_id);
                self.emit_borrow_field(handle, type_args, *offset, destinations, sources)
            }
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
        handle: DatatypeHandle,
        type_args: &[Type],
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = self.state.ctx();
        let type_args = self.state.instantiate_types(type_args);
        let struct_ty = self
            .state
            .lower_type(&handle.to_type(type_args))?
            .into_struct_type();
        let mut agg = struct_ty.get_undef();
        for (i, source) in sources.iter().enumerate() {
            let field_val = self.state.load_value(*source)?;
            agg = llvm
                .builder
                .build_insert_value(agg, field_val, to_field_index(i)?, &format!("pack_{i}"))?
                .into_struct_value();
        }
        self.state
            .store(self.state.destination(destinations, 0)?, agg.into())?;
        Ok(())
    }

    fn emit_unpack(
        &self,
        handle: DatatypeHandle,
        type_args: &[Type],
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = self.state.ctx();
        let _type_args = self.state.instantiate_types(type_args);
        let struct_val = self.state.load_struct(self.state.source(sources, 0)?)?;
        let struct_env = self.state.ctx().get_struct_env(handle)?;
        let field_count = struct_env.get_fields().count();
        for (i, destination) in destinations.iter().enumerate().take(field_count) {
            let field_val = llvm.builder.build_extract_value(
                struct_val,
                to_field_index(i)?,
                &format!("unpack_{i}"),
            )?;
            self.state.store(*destination, field_val)?;
        }
        Ok(())
    }

    fn emit_borrow_loc(&self, destinations: &[usize], sources: &[usize]) -> CompileResult<()> {
        let ptr = self.state.get_local(self.state.source(sources, 0)?)?.alloca;
        self.state
            .store(self.state.destination(destinations, 0)?, ptr.into())?;
        Ok(())
    }

    fn emit_borrow_field(
        &self,
        handle: DatatypeHandle,
        type_args: &[Type],
        offset: usize,
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = self.state.ctx();
        let struct_ptr = self.state.load_pointer(self.state.source(sources, 0)?)?;
        let type_args = self.state.instantiate_types(type_args);
        let struct_ty = self.state.lower_type(&handle.to_type(type_args))?;
        let field_ptr = llvm.builder.build_struct_gep(
            struct_ty,
            struct_ptr,
            to_field_index(offset)?,
            "borrow_field",
        )?;
        self.state
            .store(self.state.destination(destinations, 0)?, field_ptr.into())?;
        Ok(())
    }

    fn emit_get_field(
        &self,
        offset: usize,
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = self.state.ctx();
        let struct_val = self.state.load_struct(self.state.source(sources, 0)?)?;
        let field_val =
            llvm.builder
                .build_extract_value(struct_val, to_field_index(offset)?, "getfield")?;
        self.state
            .store(self.state.destination(destinations, 0)?, field_val)?;
        Ok(())
    }

    fn emit_read_ref(&self, destinations: &[usize], sources: &[usize]) -> CompileResult<()> {
        let llvm = self.state.ctx();
        let ptr = self.state.load_pointer(self.state.source(sources, 0)?)?;
        let pointee_ty = self.state.pointee_type(self.state.source(sources, 0)?)?;
        let val = llvm.builder.build_load(pointee_ty, ptr, "read_ref")?;
        self.state
            .store(self.state.destination(destinations, 0)?, val)?;
        Ok(())
    }

    fn emit_write_ref(&self, sources: &[usize]) -> CompileResult<()> {
        let llvm = self.state.ctx();
        let ptr = self.state.load_pointer(self.state.source(sources, 0)?)?;
        let val = self.state.load_value(self.state.source(sources, 1)?)?;
        llvm.builder.build_store(ptr, val)?;
        Ok(())
    }

    fn emit_freeze_ref(&self, destinations: &[usize], sources: &[usize]) -> CompileResult<()> {
        let ptr = self.state.load_value(self.state.source(sources, 0)?)?;
        self.state
            .store(self.state.destination(destinations, 0)?, ptr)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use move_binary_format::file_format::{
        Bytecode, DatatypeHandleIndex, FieldHandleIndex, SignatureToken, StructDefinitionIndex,
    };

    use crate::module::CompiledModuleBuilder;

    #[test]
    fn pack_struct() {
        let pt = SignatureToken::Datatype(DatatypeHandleIndex(0));
        let asm = CompiledModuleBuilder::point()
            .function(
                "new_point",
                vec![SignatureToken::U64, SignatureToken::U64],
                vec![pt],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::CopyLoc(1),
                    Bytecode::Pack(StructDefinitionIndex(0)),
                    Bytecode::Ret,
                ],
            )
            .compile();
        assert!(
            asm.contains("0x0_M_new_point"),
            "missing '0x0_M_new_point' symbol\n{asm}"
        );
    }

    #[test]
    fn unpack_struct() {
        let pt = SignatureToken::Datatype(DatatypeHandleIndex(0));
        let asm = CompiledModuleBuilder::point()
            .function(
                "get_x",
                vec![pt],
                vec![SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![
                    Bytecode::MoveLoc(0),
                    Bytecode::Unpack(StructDefinitionIndex(0)),
                    Bytecode::StLoc(2), // y (discarded)
                    Bytecode::StLoc(1), // x
                    Bytecode::MoveLoc(1),
                    Bytecode::Ret,
                ],
            )
            .compile();
        assert!(
            asm.contains("0x0_M_get_x"),
            "missing '0x0_M_get_x' symbol\n{asm}"
        );
    }

    #[test]
    fn borrow_and_read_ref() {
        let asm = CompiledModuleBuilder::new()
            .function(
                "copy_via_ref",
                vec![SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![SignatureToken::Reference(Box::new(SignatureToken::U64))],
                vec![
                    Bytecode::ImmBorrowLoc(0), // &x
                    Bytecode::StLoc(1),        // r = &x
                    Bytecode::MoveLoc(1),      // push r
                    Bytecode::ReadRef,         // *r
                    Bytecode::Ret,
                ],
            )
            .compile();
        assert!(asm.contains("0x0_M_copy_via_ref"), "missing symbol\n{asm}");
    }

    #[test]
    fn write_ref() {
        let mut_ref = SignatureToken::MutableReference(Box::new(SignatureToken::U64));
        let asm = CompiledModuleBuilder::new()
            .function(
                "overwrite",
                vec![SignatureToken::U64, SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![mut_ref],
                vec![
                    Bytecode::MutBorrowLoc(0), // &mut x
                    Bytecode::StLoc(2),        // r = &mut x
                    Bytecode::CopyLoc(1),      // push y (value)
                    Bytecode::CopyLoc(2),      // push r (ref)
                    Bytecode::WriteRef,        // *r = y
                    Bytecode::MoveLoc(2),      // push r
                    Bytecode::ReadRef,         // *r
                    Bytecode::Ret,
                ],
            )
            .compile();
        assert!(asm.contains("0x0_M_overwrite"), "missing symbol\n{asm}");
    }

    #[test]
    fn freeze_ref() {
        let mut_ref = SignatureToken::MutableReference(Box::new(SignatureToken::U64));
        let imm_ref = SignatureToken::Reference(Box::new(SignatureToken::U64));
        let asm = CompiledModuleBuilder::new()
            .function(
                "freeze",
                vec![SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![mut_ref, imm_ref],
                vec![
                    Bytecode::MutBorrowLoc(0), // &mut x
                    Bytecode::StLoc(1),        // r_mut = &mut x
                    Bytecode::MoveLoc(1),      // push r_mut
                    Bytecode::FreezeRef,       // &mut → &
                    Bytecode::StLoc(2),        // r_imm = freeze(r_mut)
                    Bytecode::MoveLoc(2),      // push r_imm
                    Bytecode::ReadRef,         // *r_imm
                    Bytecode::Ret,
                ],
            )
            .compile();
        assert!(asm.contains("0x0_M_freeze"), "missing symbol\n{asm}");
    }

    #[test]
    fn borrow_field() {
        let pt = SignatureToken::Datatype(DatatypeHandleIndex(0));
        let ref_point = SignatureToken::Reference(Box::new(pt.clone()));
        let ref_u64 = SignatureToken::Reference(Box::new(SignatureToken::U64));
        let asm = CompiledModuleBuilder::point()
            .field_handle(StructDefinitionIndex(0), 0) // FieldHandleIndex(0) → Point.x
            .function(
                "get_x_via_ref",
                vec![SignatureToken::U64, SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![pt, ref_point, ref_u64],
                vec![
                    Bytecode::CopyLoc(0),                          // push x
                    Bytecode::CopyLoc(1),                          // push y
                    Bytecode::Pack(StructDefinitionIndex(0)),      // Point { x, y }
                    Bytecode::StLoc(2),                            // p = ...
                    Bytecode::ImmBorrowLoc(2),                     // &p
                    Bytecode::StLoc(3),                            // ref_p = &p
                    Bytecode::MoveLoc(3),                          // push ref_p
                    Bytecode::ImmBorrowField(FieldHandleIndex(0)), // &ref_p.x
                    Bytecode::StLoc(4),                            // ref_x = ...
                    Bytecode::MoveLoc(4),                          // push ref_x
                    Bytecode::ReadRef,                             // *ref_x
                    Bytecode::Ret,
                ],
            )
            .compile();
        assert!(asm.contains("0x0_M_get_x_via_ref"), "missing symbol\n{asm}");
    }
}
