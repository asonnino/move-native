// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

mod arithmetic;
mod calls;
mod constants;
mod control_flow;
mod state;
mod storage;
mod structs;

use std::collections::BTreeMap;

use inkwell::values::FunctionValue;
use move_model::ty::Type;
use move_stackless_bytecode::function_target::FunctionData;
use move_stackless_bytecode::stackless_bytecode::{AssignKind, Bytecode, Operation};

use crate::context::LlvmContext;
use crate::error::{CompileError, CompileResult};
use crate::types::TypeLowering;

pub(crate) use state::{FunctionState, Local};

use arithmetic::ArithmeticEmitter;
use calls::CallEmitter;
use constants::ConstantEmitter;
use control_flow::ControlFlowEmitter;
use storage::StorageEmitter;
use structs::StructEmitter;

/// Per-function lowering orchestrator.
///
/// Uses the alloca/mem2reg pattern: each stackless bytecode temp is mapped to
/// an LLVM `alloca` in the entry block. LLVM's `mem2reg` pass later promotes
/// these to SSA registers.
pub(crate) struct FunctionLowering<'a, 'ctx> {
    state: FunctionState<'a, 'ctx>,
}

impl<'a, 'ctx> FunctionLowering<'a, 'ctx> {
    pub fn new(
        ctx: &'a LlvmContext<'ctx>,
        function: FunctionValue<'ctx>,
        parameter_count: usize,
        function_data: &FunctionData,
        type_params: Vec<Type>,
    ) -> CompileResult<Self> {
        let entry = ctx.context.append_basic_block(function, "entry");
        ctx.builder.position_at_end(entry);

        let type_lowering = TypeLowering::new(ctx);

        // Allocas for all locals
        let mut locals = Vec::with_capacity(function_data.local_types.len());
        for (i, ty) in function_data.local_types.iter().enumerate() {
            let mty = if type_params.is_empty() {
                ty.clone()
            } else {
                ty.instantiate(&type_params)
            };
            let llvm_ty = type_lowering.lower_type(&mty)?;
            let alloca = ctx.builder.build_alloca(llvm_ty, &format!("t{i}")).unwrap();
            locals.push(Local {
                mty,
                llvm_ty,
                alloca,
            });
        }

        // Store function parameters into their allocas
        for (i, local) in locals.iter().enumerate().take(parameter_count) {
            let param = function.get_nth_param(i as u32).unwrap();
            ctx.builder.build_store(local.alloca, param).unwrap();
        }

        // Pre-create basic blocks for all labels
        let mut label_blocks = BTreeMap::new();
        for bc in &function_data.code {
            if let Bytecode::Label(_, label) = bc {
                let block = ctx
                    .context
                    .append_basic_block(function, &format!("L{}", label.as_usize()));
                label_blocks.insert(*label, block);
            }
        }

        Ok(Self {
            state: FunctionState::new(ctx, locals, label_blocks, type_params),
        })
    }

    pub fn lower_function(&self, function_data: &FunctionData) -> CompileResult<()> {
        for bc in &function_data.code {
            self.lower_bytecode(bc)?;
        }
        Ok(())
    }

    fn lower_bytecode(&self, bc: &Bytecode) -> CompileResult<()> {
        match bc {
            Bytecode::Assign(_, dst, src, kind) => {
                // Move-swap optimization: for Move of struct types, swap the
                // local slots instead of load+store. Move guarantees the source
                // is dead after this point, so reusing its alloca is safe and
                // avoids an unnecessary copy.
                if matches!(kind, AssignKind::Move)
                    && self.state.locals.borrow()[*src].mty.is_struct()
                {
                    let cloned = self.state.locals.borrow()[*src].clone();
                    self.state.locals.borrow_mut()[*dst] = cloned;
                } else {
                    let val = self.state.load_value(*src)?;
                    self.state.store(*dst, val);
                }
            }
            Bytecode::Load(_, dst, constant) => {
                let val = ConstantEmitter::new(&self.state).lower(constant)?;
                self.state.store(*dst, val);
            }
            Bytecode::Call(_, dsts, op, srcs, _) => {
                self.lower_operation(dsts, op, srcs)?;
            }
            Bytecode::Nop(_) => {}
            // Control flow: Ret, Label, Jump, Branch, Abort (+ catch-all)
            other => ControlFlowEmitter::new(&self.state).emit(other)?,
        }
        Ok(())
    }

    fn lower_operation(&self, dsts: &[usize], op: &Operation, srcs: &[usize]) -> CompileResult<()> {
        match op {
            // Arithmetic, comparisons, bitwise, shifts, logical, casts
            Operation::Add
            | Operation::Sub
            | Operation::Mul
            | Operation::Div
            | Operation::Mod
            | Operation::Lt
            | Operation::Gt
            | Operation::Le
            | Operation::Ge
            | Operation::Eq
            | Operation::Neq
            | Operation::BitAnd
            | Operation::BitOr
            | Operation::Xor
            | Operation::Shl
            | Operation::Shr
            | Operation::And
            | Operation::Or
            | Operation::Not
            | Operation::CastU8
            | Operation::CastU16
            | Operation::CastU32
            | Operation::CastU64
            | Operation::CastU128
            | Operation::CastU256 => ArithmeticEmitter::new(&self.state).emit(dsts, op, srcs),

            // Struct and reference operations
            Operation::Pack(..)
            | Operation::Unpack(..)
            | Operation::BorrowLoc
            | Operation::BorrowField(..)
            | Operation::GetField(..)
            | Operation::ReadRef
            | Operation::WriteRef
            | Operation::FreezeRef
            | Operation::Destroy => StructEmitter::new(&self.state).emit(dsts, op, srcs),

            // Function calls
            Operation::Function(module_id, fun_id, type_args) => {
                CallEmitter::new(&self.state).emit(dsts, *module_id, *fun_id, type_args, srcs)
            }

            // Global storage operations
            Operation::MoveTo(mid, did, type_args) => {
                StorageEmitter::new(&self.state).emit_move_to(*mid, *did, type_args, dsts, srcs)
            }
            Operation::MoveFrom(mid, did, type_args) => {
                StorageEmitter::new(&self.state).emit_move_from(*mid, *did, type_args, dsts, srcs)
            }
            Operation::Exists(mid, did, type_args) => {
                StorageEmitter::new(&self.state).emit_exists(*mid, *did, type_args, dsts, srcs)
            }
            Operation::BorrowGlobal(mid, did, type_args) => StorageEmitter::new(&self.state)
                .emit_borrow_global(*mid, *did, type_args, dsts, srcs),
            Operation::GetGlobal(mid, did, type_args) => {
                StorageEmitter::new(&self.state).emit_get_global(*mid, *did, type_args, dsts, srcs)
            }

            other => Err(CompileError::UnsupportedOperation(format!("{:?}", other))),
        }
    }
}
