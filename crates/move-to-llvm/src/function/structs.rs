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
        let struct_val = self.state.load_struct(sources[0])?;
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
        let ptr = self.state.get_local(sources[0])?.alloca;
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
        let struct_ptr = self.state.load_pointer(sources[0])?;
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
        let struct_val = self.state.load_struct(sources[0])?;
        let field_val = llvm
            .builder
            .build_extract_value(struct_val, offset as u32, "getfield")?;
        self.state.store(destinations[0], field_val)?;
        Ok(())
    }

    fn emit_read_ref(&self, destinations: &[usize], sources: &[usize]) -> CompileResult<()> {
        let llvm = self.state.ctx;
        let ptr = self.state.load_pointer(sources[0])?;
        let pointee_ty = self.state.pointee_type(sources[0])?;
        let val = llvm.builder.build_load(pointee_ty, ptr, "read_ref")?;
        self.state.store(destinations[0], val)?;
        Ok(())
    }

    fn emit_write_ref(&self, sources: &[usize]) -> CompileResult<()> {
        let llvm = self.state.ctx;
        let ptr = self.state.load_pointer(sources[0])?;
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

#[cfg(test)]
mod tests {
    use move_binary_format::file_format::{
        AbilitySet, Bytecode, DatatypeHandleIndex, FieldHandleIndex, SignatureToken,
        StructDefinitionIndex,
    };

    use crate::compiler::Compiler;
    use crate::module::CompiledModuleBuilder;
    use crate::target::Target;

    /// Module builder pre-loaded with `Point { x: u64, y: u64 }` at `DatatypeHandleIndex(0)`.
    fn point_module() -> CompiledModuleBuilder {
        CompiledModuleBuilder::new().struct_definition(
            "Point",
            AbilitySet::PRIMITIVES,
            vec![("x", SignatureToken::U64), ("y", SignatureToken::U64)],
        )
    }

    fn point_token() -> SignatureToken {
        SignatureToken::Datatype(DatatypeHandleIndex(0))
    }

    #[test]
    fn pack_struct() {
        let module = point_module()
            .function(
                "new_point",
                vec![SignatureToken::U64, SignatureToken::U64],
                vec![point_token()],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::CopyLoc(1),
                    Bytecode::Pack(StructDefinitionIndex(0)),
                    Bytecode::Ret,
                ],
            )
            .build();

        let asm = Compiler::compile_module(&Target::Aarch64, &module)
            .unwrap()
            .to_string();
        assert!(
            asm.contains("new_point"),
            "missing 'new_point' symbol\n{asm}"
        );
    }

    #[test]
    fn unpack_struct() {
        let module = point_module()
            .function(
                "get_x",
                vec![point_token()],
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
            .build();

        let asm = Compiler::compile_module(&Target::Aarch64, &module)
            .unwrap()
            .to_string();
        assert!(asm.contains("get_x"), "missing 'get_x' symbol\n{asm}");
    }

    #[test]
    fn borrow_and_read_ref() {
        // copy_via_ref(x: u64): u64 { let r = &x; *r }
        let module = CompiledModuleBuilder::new()
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
            .build();

        let asm = Compiler::compile_module(&Target::Aarch64, &module)
            .unwrap()
            .to_string();
        assert!(asm.contains("copy_via_ref"), "missing symbol\n{asm}");
    }

    #[test]
    fn write_ref() {
        // overwrite(x: u64, y: u64): u64 { let r = &mut x; *r = y; *r }
        let mut_ref = SignatureToken::MutableReference(Box::new(SignatureToken::U64));
        let module = CompiledModuleBuilder::new()
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
            .build();

        let asm = Compiler::compile_module(&Target::Aarch64, &module)
            .unwrap()
            .to_string();
        assert!(asm.contains("overwrite"), "missing symbol\n{asm}");
    }

    #[test]
    fn borrow_field() {
        // get_x_via_ref(x: u64, y: u64): u64 { let p = Point{x,y}; let r = &p; *(&r.x) }
        let ref_point = SignatureToken::Reference(Box::new(point_token()));
        let ref_u64 = SignatureToken::Reference(Box::new(SignatureToken::U64));
        let module = point_module()
            .field_handle(StructDefinitionIndex(0), 0) // FieldHandleIndex(0) → Point.x
            .function(
                "get_x_via_ref",
                vec![SignatureToken::U64, SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![point_token(), ref_point, ref_u64],
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
            .build();

        let asm = Compiler::compile_module(&Target::Aarch64, &module)
            .unwrap()
            .to_string();
        assert!(asm.contains("get_x_via_ref"), "missing symbol\n{asm}");
    }
}
