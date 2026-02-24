// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::module::Linkage;
use inkwell::types::BasicType;
use move_model::model::{DatatypeId, ModuleId};
use move_model::ty::Type;

use super::FunctionLowering;
use crate::error::CompileResult;

/// Emits LLVM calls for Move global storage operations
/// (MoveTo, MoveFrom, Exists, BorrowGlobal, GetGlobal).
pub(crate) struct StorageEmitter<'a, 'b, 'ctx> {
    fl: &'a FunctionLowering<'b, 'ctx>,
}

impl<'a, 'b, 'ctx> StorageEmitter<'a, 'b, 'ctx> {
    pub fn new(fl: &'a FunctionLowering<'b, 'ctx>) -> Self {
        Self { fl }
    }

    pub fn emit_move_to(
        &self,
        mid: ModuleId,
        did: DatatypeId,
        type_args: &[Type],
        dsts: &[usize],
        srcs: &[usize],
    ) -> CompileResult<()> {
        let ctx = &self.fl.compiler.ctx;
        self.emit_storage_call("move_to", mid, did, type_args, dsts, srcs, |dt_ty| {
            let val_ty = self.fl.compiler.lower_type(&dt_ty)?.into();
            Ok(ctx
                .context
                .void_type()
                .fn_type(&[val_ty, ctx.i256_type.into()], false))
        })
    }

    pub fn emit_move_from(
        &self,
        mid: ModuleId,
        did: DatatypeId,
        type_args: &[Type],
        dsts: &[usize],
        srcs: &[usize],
    ) -> CompileResult<()> {
        let ctx = &self.fl.compiler.ctx;
        self.emit_storage_call("move_from", mid, did, type_args, dsts, srcs, |dt_ty| {
            let ret_ty = self.fl.compiler.lower_type(&dt_ty)?;
            Ok(ret_ty.fn_type(&[ctx.i256_type.into()], false))
        })
    }

    pub fn emit_exists(
        &self,
        mid: ModuleId,
        did: DatatypeId,
        type_args: &[Type],
        dsts: &[usize],
        srcs: &[usize],
    ) -> CompileResult<()> {
        let ctx = &self.fl.compiler.ctx;
        self.emit_storage_call("exists", mid, did, type_args, dsts, srcs, |_| {
            Ok(ctx.i8_type.fn_type(&[ctx.i256_type.into()], false))
        })
    }

    pub fn emit_borrow_global(
        &self,
        mid: ModuleId,
        did: DatatypeId,
        type_args: &[Type],
        dsts: &[usize],
        srcs: &[usize],
    ) -> CompileResult<()> {
        let ctx = &self.fl.compiler.ctx;
        self.emit_storage_call("borrow_global", mid, did, type_args, dsts, srcs, |_| {
            Ok(ctx.ptr_type.fn_type(&[ctx.i256_type.into()], false))
        })
    }

    pub fn emit_get_global(
        &self,
        mid: ModuleId,
        did: DatatypeId,
        type_args: &[Type],
        dsts: &[usize],
        srcs: &[usize],
    ) -> CompileResult<()> {
        let ctx = &self.fl.compiler.ctx;
        self.emit_storage_call("get_global", mid, did, type_args, dsts, srcs, |dt_ty| {
            let ret_ty = self.fl.compiler.lower_type(&dt_ty)?;
            Ok(ret_ty.fn_type(&[ctx.i256_type.into()], false))
        })
    }

    /// Common implementation for all storage operations.
    #[allow(clippy::too_many_arguments)]
    fn emit_storage_call(
        &self,
        op_name: &str,
        mid: ModuleId,
        did: DatatypeId,
        type_args: &[Type],
        dsts: &[usize],
        srcs: &[usize],
        build_fn_type: impl FnOnce(Type) -> CompileResult<inkwell::types::FunctionType<'ctx>>,
    ) -> CompileResult<()> {
        let ctx = &self.fl.compiler.ctx;
        let inst_args = self.fl.inst_types(type_args);
        let dt_ty = Type::Datatype(mid, did, inst_args);
        let mangled = self.fl.compiler.mangle_type(&dt_ty);
        let symbol = format!("__move_rt_{op_name}${mangled}");

        let func = match ctx.module.get_function(&symbol) {
            Some(f) => f,
            None => {
                let fn_type = build_fn_type(dt_ty)?;
                ctx.module
                    .add_function(&symbol, fn_type, Some(Linkage::External))
            }
        };

        let args: Vec<_> = srcs
            .iter()
            .map(|s| self.fl.load_value(*s).map(|v| v.into()))
            .collect::<Result<_, _>>()?;

        let call = ctx.builder.build_call(func, &args, &symbol).unwrap();

        if !dsts.is_empty() {
            let ret_val = match call.try_as_basic_value() {
                inkwell::values::ValueKind::Basic(v) => v,
                _ => panic!("expected non-void return from {symbol}"),
            };
            self.fl.store(dsts[0], ret_val);
        }
        Ok(())
    }
}
