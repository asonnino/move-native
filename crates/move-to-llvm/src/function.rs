// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;

use inkwell::IntPredicate;
use inkwell::basic_block::BasicBlock;
use inkwell::values::{FunctionValue, IntValue, PointerValue};
use move_model::model::FunctionEnv;
use move_model::ty::Type;
use move_stackless_bytecode::function_target::FunctionData;
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Constant, Label, Operation};

use crate::context::LlvmContext;
use crate::error::CompileError;
use crate::types::lower_model_type;

/// Per-function lowering state.
///
/// Uses the alloca/mem2reg pattern: each stackless bytecode temp is mapped to
/// an LLVM `alloca` in the entry block. LLVM's `mem2reg` pass later promotes
/// these to SSA registers.
struct FunctionLowering<'a, 'ctx> {
    ctx: &'a LlvmContext<'ctx>,
    /// Allocas for each temp (params + locals + compiler-generated temps).
    temps: Vec<PointerValue<'ctx>>,
    /// Types of each temp, from `FunctionData::local_types`.
    temp_types: Vec<Type>,
    /// Pre-created basic blocks for each Label in the bytecode.
    label_blocks: BTreeMap<Label, BasicBlock<'ctx>>,
}

impl<'a, 'ctx> FunctionLowering<'a, 'ctx> {
    fn new(
        ctx: &'a LlvmContext<'ctx>,
        function: FunctionValue<'ctx>,
        param_count: usize,
        func_data: &FunctionData,
    ) -> Result<Self, CompileError> {
        let entry = ctx.context.append_basic_block(function, "entry");
        ctx.builder.position_at_end(entry);

        // Allocas for all temps
        let mut temps = Vec::with_capacity(func_data.local_types.len());
        for (i, ty) in func_data.local_types.iter().enumerate() {
            let llvm_ty = lower_model_type(ctx, ty)?;
            let alloca = ctx.builder.build_alloca(llvm_ty, &format!("t{i}")).unwrap();
            temps.push(alloca);
        }

        // Store function parameters into their allocas
        for (i, alloca) in temps.iter().enumerate().take(param_count) {
            let param = function.get_nth_param(i as u32).unwrap().into_int_value();
            ctx.builder.build_store(*alloca, param).unwrap();
        }

        // Pre-create basic blocks for all labels
        let mut label_blocks = BTreeMap::new();
        for bc in &func_data.code {
            if let Bytecode::Label(_, label) = bc {
                let block = ctx
                    .context
                    .append_basic_block(function, &format!("L{}", label.as_usize()));
                label_blocks.insert(*label, block);
            }
        }

        Ok(Self {
            ctx,
            temps,
            temp_types: func_data.local_types.clone(),
            label_blocks,
        })
    }

    fn lower_code(&mut self, func_data: &FunctionData) -> Result<(), CompileError> {
        for bc in &func_data.code {
            self.lower_bytecode(bc)?;
        }
        Ok(())
    }

    fn lower_bytecode(&mut self, bc: &Bytecode) -> Result<(), CompileError> {
        match bc {
            Bytecode::Assign(_, dst, src, _) => {
                let val = self.load_temp(*src)?;
                self.ctx.builder.build_store(self.temps[*dst], val).unwrap();
            }
            Bytecode::Load(_, dst, constant) => {
                let val = self.lower_constant(constant)?;
                self.ctx.builder.build_store(self.temps[*dst], val).unwrap();
            }
            Bytecode::Call(_, dsts, op, srcs, _) => {
                self.lower_operation(dsts, op, srcs)?;
            }
            Bytecode::Ret(_, rets) => {
                if rets.is_empty() {
                    self.ctx.builder.build_return(None).unwrap();
                } else {
                    let val = self.load_temp(rets[0])?;
                    self.ctx.builder.build_return(Some(&val)).unwrap();
                }
            }
            Bytecode::Label(_, label) => {
                let block = self.label_blocks[label];
                // Add fallthrough branch if current block has no terminator
                let current = self.ctx.builder.get_insert_block().unwrap();
                if current.get_terminator().is_none() {
                    self.ctx.builder.build_unconditional_branch(block).unwrap();
                }
                self.ctx.builder.position_at_end(block);
            }
            Bytecode::Jump(_, label) => {
                let block = self.label_blocks[label];
                self.ctx.builder.build_unconditional_branch(block).unwrap();
            }
            Bytecode::Branch(_, then_label, else_label, cond) => {
                let cond_val = self.load_temp(*cond)?;
                let zero = cond_val.get_type().const_zero();
                let cmp = self
                    .ctx
                    .builder
                    .build_int_compare(IntPredicate::NE, cond_val, zero, "cond")
                    .unwrap();
                let then_block = self.label_blocks[then_label];
                let else_block = self.label_blocks[else_label];
                self.ctx
                    .builder
                    .build_conditional_branch(cmp, then_block, else_block)
                    .unwrap();
            }
            Bytecode::Abort(_, _) => {
                self.ctx.builder.build_unreachable().unwrap();
            }
            Bytecode::Nop(_) => {}
            other => {
                return Err(CompileError::UnsupportedBytecode(format!("{:?}", other)));
            }
        }
        Ok(())
    }

    fn load_temp(&self, idx: usize) -> Result<IntValue<'ctx>, CompileError> {
        let ty = lower_model_type(self.ctx, &self.temp_types[idx])?;
        Ok(self
            .ctx
            .builder
            .build_load(ty, self.temps[idx], &format!("t{idx}"))
            .unwrap()
            .into_int_value())
    }

    fn lower_constant(&self, constant: &Constant) -> Result<IntValue<'ctx>, CompileError> {
        match constant {
            Constant::Bool(v) => Ok(self.ctx.i8_type.const_int(*v as u64, false)),
            Constant::U8(v) => Ok(self.ctx.i8_type.const_int(*v as u64, false)),
            Constant::U16(v) => Ok(self.ctx.i16_type.const_int(*v as u64, false)),
            Constant::U32(v) => Ok(self.ctx.i32_type.const_int(*v as u64, false)),
            Constant::U64(v) => Ok(self.ctx.i64_type.const_int(*v, false)),
            Constant::U128(v) => {
                let words = [*v as u64, (*v >> 64) as u64];
                Ok(self.ctx.i128_type.const_int_arbitrary_precision(&words))
            }
            other => Err(CompileError::UnsupportedOperation(format!(
                "constant: {:?}",
                other
            ))),
        }
    }

    fn lower_operation(
        &self,
        dsts: &[usize],
        op: &Operation,
        srcs: &[usize],
    ) -> Result<(), CompileError> {
        match op {
            Operation::Add | Operation::Sub | Operation::Mul | Operation::Div | Operation::Mod => {
                let lhs = self.load_temp(srcs[0])?;
                let rhs = self.load_temp(srcs[1])?;
                let result = match op {
                    Operation::Add => self.ctx.builder.build_int_add(lhs, rhs, "add").unwrap(),
                    Operation::Sub => self.ctx.builder.build_int_sub(lhs, rhs, "sub").unwrap(),
                    Operation::Mul => self.ctx.builder.build_int_mul(lhs, rhs, "mul").unwrap(),
                    Operation::Div => self
                        .ctx
                        .builder
                        .build_int_unsigned_div(lhs, rhs, "div")
                        .unwrap(),
                    Operation::Mod => self
                        .ctx
                        .builder
                        .build_int_unsigned_rem(lhs, rhs, "mod")
                        .unwrap(),
                    _ => unreachable!(),
                };
                self.ctx
                    .builder
                    .build_store(self.temps[dsts[0]], result)
                    .unwrap();
                Ok(())
            }
            other => Err(CompileError::UnsupportedOperation(format!("{:?}", other))),
        }
    }
}

/// Lower a single function into the LLVM module using stackless bytecode.
pub fn lower_function<'ctx>(
    ctx: &LlvmContext<'ctx>,
    func_env: &FunctionEnv<'_>,
    func_data: &FunctionData,
) -> Result<(), CompileError> {
    let name = func_env
        .module_env
        .env
        .symbol_pool()
        .string(func_env.get_name());
    let param_count = func_env.get_parameter_count();

    // Build LLVM parameter types
    let param_llvm_types: Vec<_> = func_data.local_types[..param_count]
        .iter()
        .map(|ty| lower_model_type(ctx, ty).map(|t| t.into()))
        .collect::<Result<_, _>>()?;

    // Build LLVM function type
    let fn_type = if func_data.return_types.is_empty() {
        ctx.context.void_type().fn_type(&param_llvm_types, false)
    } else if func_data.return_types.len() == 1 {
        let ret_type = lower_model_type(ctx, &func_data.return_types[0])?;
        ret_type.fn_type(&param_llvm_types, false)
    } else {
        return Err(CompileError::UnsupportedType(
            "multi-value return".to_string(),
        ));
    };

    let function = ctx.module.add_function(&name, fn_type, None);

    let mut lowering = FunctionLowering::new(ctx, function, param_count, func_data)?;
    lowering.lower_code(func_data)?;

    Ok(())
}
