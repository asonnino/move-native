// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::types::BasicType;
use move_model::model::{DatatypeId, ModuleId};
use move_model::ty::Type;

use super::state::FunctionState;
use crate::error::CompileResult;

/// Emits LLVM calls for Move global storage operations
/// (MoveTo, MoveFrom, Exists, BorrowGlobal, GetGlobal).
pub(crate) struct StorageEmitter<'a, 'b, 'ctx> {
    state: &'a FunctionState<'b, 'ctx>,
}

impl<'a, 'b, 'ctx> StorageEmitter<'a, 'b, 'ctx> {
    pub fn new(state: &'a FunctionState<'b, 'ctx>) -> Self {
        Self { state }
    }

    pub fn emit_move_to(
        &self,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        type_args: &[Type],
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = &self.state.ctx;
        self.emit_storage_call(
            "move_to",
            module_id,
            datatype_id,
            type_args,
            destinations,
            sources,
            |dt_ty| {
                let val_ty = self.state.lower_type(&dt_ty)?.into();
                Ok(llvm
                    .context
                    .void_type()
                    .fn_type(&[val_ty, llvm.i256_type.into()], false))
            },
        )
    }

    pub fn emit_move_from(
        &self,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        type_args: &[Type],
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = &self.state.ctx;
        self.emit_storage_call(
            "move_from",
            module_id,
            datatype_id,
            type_args,
            destinations,
            sources,
            |dt_ty| {
                let ret_ty = self.state.lower_type(&dt_ty)?;
                Ok(ret_ty.fn_type(&[llvm.i256_type.into()], false))
            },
        )
    }

    pub fn emit_exists(
        &self,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        type_args: &[Type],
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = &self.state.ctx;
        self.emit_storage_call(
            "exists",
            module_id,
            datatype_id,
            type_args,
            destinations,
            sources,
            |_| Ok(llvm.i8_type.fn_type(&[llvm.i256_type.into()], false)),
        )
    }

    pub fn emit_borrow_global(
        &self,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        type_args: &[Type],
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = &self.state.ctx;
        self.emit_storage_call(
            "borrow_global",
            module_id,
            datatype_id,
            type_args,
            destinations,
            sources,
            |_| Ok(llvm.ptr_type.fn_type(&[llvm.i256_type.into()], false)),
        )
    }

    pub fn emit_get_global(
        &self,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        type_args: &[Type],
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = &self.state.ctx;
        self.emit_storage_call(
            "get_global",
            module_id,
            datatype_id,
            type_args,
            destinations,
            sources,
            |dt_ty| {
                let ret_ty = self.state.lower_type(&dt_ty)?;
                Ok(ret_ty.fn_type(&[llvm.i256_type.into()], false))
            },
        )
    }

    /// Common implementation for all storage operations.
    #[allow(clippy::too_many_arguments)]
    fn emit_storage_call(
        &self,
        operation_name: &str,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        type_args: &[Type],
        destinations: &[usize],
        sources: &[usize],
        build_fn_type: impl FnOnce(Type) -> CompileResult<inkwell::types::FunctionType<'ctx>>,
    ) -> CompileResult<()> {
        let llvm = &self.state.ctx;
        let inst_args = self.state.inst_types(type_args);
        let dt_ty = Type::Datatype(module_id, datatype_id, inst_args);
        let mangled = self.state.mangle_type(&dt_ty)?;
        let symbol = format!("__move_rt_{operation_name}${mangled}");

        let fn_type = build_fn_type(dt_ty)?;
        let func = llvm.add_external_function(&symbol, fn_type);

        let args: Vec<_> = sources
            .iter()
            .map(|s| self.state.load_value(*s).map(|v| v.into()))
            .collect::<Result<_, _>>()?;

        let call = llvm.builder.build_call(func, &args, &symbol)?;

        if !destinations.is_empty() {
            let ret_val = match call.try_as_basic_value() {
                inkwell::values::ValueKind::Basic(v) => v,
                _ => panic!("expected non-void return from {symbol}"),
            };
            self.state.store(destinations[0], ret_val)?;
        }
        Ok(())
    }
}
