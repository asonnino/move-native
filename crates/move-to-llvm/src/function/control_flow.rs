// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::IntPredicate;
use inkwell::types::BasicTypeEnum;
use move_stackless_bytecode::stackless_bytecode::Bytecode;

use super::state::FunctionState;
use crate::error::{CompileError, CompileResult};

/// Emits LLVM IR for control-flow bytecodes
/// (Ret, Label, Jump, Branch, Abort).
pub(crate) struct ControlFlowEmitter<'a, 'b, 'ctx> {
    state: &'a FunctionState<'b, 'ctx>,
}

impl<'a, 'b, 'ctx> ControlFlowEmitter<'a, 'b, 'ctx> {
    pub fn new(state: &'a FunctionState<'b, 'ctx>) -> Self {
        Self { state }
    }

    pub fn emit(&self, bc: &Bytecode) -> CompileResult<()> {
        let llvm = self.state.ctx;
        match bc {
            Bytecode::Ret(_, rets) => {
                if rets.is_empty() {
                    llvm.builder.build_return(None)?;
                } else if rets.len() == 1 {
                    let val = self.state.load_value(rets[0])?;
                    llvm.builder.build_return(Some(&val))?;
                } else {
                    // Multi-return: pack values into an anonymous struct
                    let locals = self.state.locals.borrow();
                    let ret_types: Vec<BasicTypeEnum<'ctx>> = rets
                        .iter()
                        .map(|r| Ok(locals[*r].llvm_ty))
                        .collect::<CompileResult<_>>()?;
                    let ret_struct_ty = llvm.context.struct_type(&ret_types, false);
                    let mut agg = ret_struct_ty.get_undef();
                    for (i, r) in rets.iter().enumerate() {
                        let val = self.state.load_value(*r)?;
                        agg = llvm
                            .builder
                            .build_insert_value(agg, val, i as u32, &format!("ret_{i}"))?
                            .into_struct_value();
                    }
                    llvm.builder.build_return(Some(&agg))?;
                }
            }
            Bytecode::Label(_, label) => {
                let block = self.state.label_blocks[label];
                // Add fallthrough branch if current block has no terminator
                let current = llvm
                    .builder
                    .get_insert_block()
                    .ok_or(CompileError::Llvm("no insert block".into()))?;
                if current.get_terminator().is_none() {
                    llvm.builder.build_unconditional_branch(block)?;
                }
                llvm.builder.position_at_end(block);
            }
            Bytecode::Jump(_, label) => {
                let block = self.state.label_blocks[label];
                llvm.builder.build_unconditional_branch(block)?;
            }
            Bytecode::Branch(_, then_label, else_label, cond) => {
                let cond_val = self.state.load_int(*cond)?;
                let zero = cond_val.get_type().const_zero();
                let cmp =
                    llvm.builder
                        .build_int_compare(IntPredicate::NE, cond_val, zero, "cond")?;
                let then_block = self.state.label_blocks[then_label];
                let else_block = self.state.label_blocks[else_label];
                llvm.builder
                    .build_conditional_branch(cmp, then_block, else_block)?;
            }
            Bytecode::Abort(_, code_idx) => {
                let code = self.state.load_value(*code_idx)?;
                let abort_fn = self.state.declare_external(
                    "__move_rt_abort",
                    llvm.context
                        .void_type()
                        .fn_type(&[llvm.i64_type.into()], false),
                );
                llvm.builder.build_call(abort_fn, &[code.into()], "abort")?;
                llvm.builder.build_unreachable()?;
            }
            _ => unreachable!("non-control-flow bytecode routed to ControlFlowEmitter"),
        }
        Ok(())
    }
}
