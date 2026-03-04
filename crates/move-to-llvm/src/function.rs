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
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Operation};

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
            let alloca = ctx.builder.build_alloca(llvm_ty, &format!("t{i}"))?;
            locals.push(Local {
                mty,
                llvm_ty,
                alloca,
            });
        }

        // Store function parameters into their allocas
        for (i, local) in locals.iter().enumerate().take(parameter_count) {
            let parameter = function
                .get_nth_param(i as u32)
                .ok_or(CompileError::Llvm("missing parameter".into()))?;
            ctx.builder.build_store(local.alloca, parameter)?;
        }

        // Pre-create basic blocks for all labels
        let mut label_blocks = BTreeMap::new();
        for byte_code in &function_data.code {
            if let Bytecode::Label(_, label) = byte_code {
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
        for byte_code in &function_data.code {
            self.lower_bytecode(byte_code)?;
        }
        Ok(())
    }

    fn lower_bytecode(&self, byte_code: &Bytecode) -> CompileResult<()> {
        match byte_code {
            Bytecode::Assign(_, destination, source, _kind) => {
                let value = self.state.load_value(*source)?;
                self.state.store(*destination, value)?;
            }
            Bytecode::Load(_, destination, constant) => {
                ConstantEmitter::new(&self.state).emit(*destination, constant)?;
            }
            Bytecode::Call(_, destinations, operation, sources, _) => {
                self.lower_operation(destinations, operation, sources)?;
            }
            Bytecode::Nop(_) => {}
            Bytecode::Ret(..)
            | Bytecode::Label(..)
            | Bytecode::Jump(..)
            | Bytecode::Branch(..)
            | Bytecode::Abort(..) => ControlFlowEmitter::new(&self.state).emit(byte_code)?,
            other => {
                return Err(CompileError::UnsupportedBytecode(other.clone()));
            }
        }
        Ok(())
    }

    fn lower_operation(
        &self,
        destinations: &[usize],
        operation: &Operation,
        sources: &[usize],
    ) -> CompileResult<()> {
        match operation {
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
            | Operation::CastU256 => {
                ArithmeticEmitter::new(&self.state).emit(destinations, operation, sources)
            }

            // Struct and reference operations
            Operation::Pack(..)
            | Operation::Unpack(..)
            | Operation::BorrowLoc
            | Operation::BorrowField(..)
            | Operation::GetField(..)
            | Operation::ReadRef
            | Operation::WriteRef
            | Operation::FreezeRef
            | Operation::Destroy => {
                StructEmitter::new(&self.state).emit(destinations, operation, sources)
            }

            // Function calls
            Operation::Function(module_id, function_id, type_args) => CallEmitter::new(&self.state)
                .emit(destinations, *module_id, *function_id, type_args, sources),

            // Global storage operations
            Operation::MoveTo(module_id, datatype_id, type_args) => StorageEmitter::new(
                &self.state,
            )
            .emit_move_to(*module_id, *datatype_id, type_args, destinations, sources),
            Operation::MoveFrom(module_id, datatype_id, type_args) => StorageEmitter::new(
                &self.state,
            )
            .emit_move_from(*module_id, *datatype_id, type_args, destinations, sources),
            Operation::Exists(module_id, datatype_id, type_args) => StorageEmitter::new(
                &self.state,
            )
            .emit_exists(*module_id, *datatype_id, type_args, destinations, sources),
            Operation::BorrowGlobal(module_id, datatype_id, type_args) => StorageEmitter::new(
                &self.state,
            )
            .emit_borrow_global(*module_id, *datatype_id, type_args, destinations, sources),
            Operation::GetGlobal(module_id, datatype_id, type_args) => StorageEmitter::new(
                &self.state,
            )
            .emit_get_global(*module_id, *datatype_id, type_args, destinations, sources),

            other => Err(CompileError::UnsupportedOperation(other.clone())),
        }
    }
}
