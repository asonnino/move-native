// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::IntPredicate;
use inkwell::types::IntType;
use inkwell::values::IntValue;
use move_stackless_bytecode::stackless_bytecode::Operation;

use super::state::FunctionState;
use crate::error::CompileResult;

/// Emits LLVM IR for arithmetic, comparison, bitwise, shift, logical,
/// and integer-cast operations.
pub(crate) struct ArithmeticEmitter<'a, 'b, 'ctx> {
    state: &'a FunctionState<'b, 'ctx>,
}

impl<'a, 'b, 'ctx> ArithmeticEmitter<'a, 'b, 'ctx> {
    pub fn new(state: &'a FunctionState<'b, 'ctx>) -> Self {
        Self { state }
    }

    pub fn emit(&self, dsts: &[usize], op: &Operation, srcs: &[usize]) -> CompileResult<()> {
        let result = match op {
            // Arithmetic: two same-type integers -> same type
            Operation::Add | Operation::Sub | Operation::Mul | Operation::Div | Operation::Mod => {
                self.emit_arithmetic(op, srcs)?
            }

            // Comparisons: two same-type integers -> bool (i8)
            Operation::Lt | Operation::Gt | Operation::Le | Operation::Ge => {
                self.emit_ord_cmp(op, srcs)?
            }
            Operation::Eq | Operation::Neq => self.emit_eq_cmp(op, srcs)?,

            // Bitwise: two same-type integers -> same type
            Operation::BitAnd | Operation::BitOr | Operation::Xor => self.emit_bitwise(op, srcs)?,

            // Shifts: value (any width) + shift amount (u8) -> same type as value
            Operation::Shl | Operation::Shr => self.emit_shift(op, srcs)?,

            // Logical AND/OR: two bools (i8) -> bool (i8)
            Operation::And | Operation::Or => self.emit_logical_binop(op, srcs)?,

            // Logical NOT: bool (i8) -> bool (i8), implemented as XOR with 1
            Operation::Not => self.emit_not(srcs)?,

            // Integer casts
            Operation::CastU8 => self.lower_cast(srcs[0], self.state.ctx.i8_type)?,
            Operation::CastU16 => self.lower_cast(srcs[0], self.state.ctx.i16_type)?,
            Operation::CastU32 => self.lower_cast(srcs[0], self.state.ctx.i32_type)?,
            Operation::CastU64 => self.lower_cast(srcs[0], self.state.ctx.i64_type)?,
            Operation::CastU128 => self.lower_cast(srcs[0], self.state.ctx.i128_type)?,
            Operation::CastU256 => self.lower_cast(srcs[0], self.state.ctx.i256_type)?,

            _ => unreachable!("ArithmeticEmitter::emit called with non-arithmetic op"),
        };
        self.state.store(dsts[0], result.into())?;
        Ok(())
    }

    fn emit_arithmetic(&self, op: &Operation, srcs: &[usize]) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx;
        let lhs = self.state.load_int(srcs[0])?;
        let rhs = self.state.load_int(srcs[1])?;
        Ok(match op {
            Operation::Add => llvm.builder.build_int_add(lhs, rhs, "add")?,
            Operation::Sub => llvm.builder.build_int_sub(lhs, rhs, "sub")?,
            Operation::Mul => llvm.builder.build_int_mul(lhs, rhs, "mul")?,
            Operation::Div => llvm.builder.build_int_unsigned_div(lhs, rhs, "div")?,
            Operation::Mod => llvm.builder.build_int_unsigned_rem(lhs, rhs, "mod")?,
            _ => unreachable!(),
        })
    }

    fn emit_ord_cmp(&self, op: &Operation, srcs: &[usize]) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx;
        let lhs = self.state.load_int(srcs[0])?;
        let rhs = self.state.load_int(srcs[1])?;
        let pred = match op {
            Operation::Lt => IntPredicate::ULT,
            Operation::Gt => IntPredicate::UGT,
            Operation::Le => IntPredicate::ULE,
            Operation::Ge => IntPredicate::UGE,
            _ => unreachable!(),
        };
        let cmp = llvm.builder.build_int_compare(pred, lhs, rhs, "cmp")?;
        Ok(llvm
            .builder
            .build_int_z_extend(cmp, llvm.i8_type, "cmp_ext")?)
    }

    fn emit_eq_cmp(&self, op: &Operation, srcs: &[usize]) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx;
        let lhs = self.state.load_int(srcs[0])?;
        let rhs = self.state.load_int(srcs[1])?;
        let pred = if matches!(op, Operation::Eq) {
            IntPredicate::EQ
        } else {
            IntPredicate::NE
        };
        let cmp = llvm.builder.build_int_compare(pred, lhs, rhs, "cmp")?;
        Ok(llvm
            .builder
            .build_int_z_extend(cmp, llvm.i8_type, "cmp_ext")?)
    }

    fn emit_bitwise(&self, op: &Operation, srcs: &[usize]) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx;
        let lhs = self.state.load_int(srcs[0])?;
        let rhs = self.state.load_int(srcs[1])?;
        Ok(match op {
            Operation::BitAnd => llvm.builder.build_and(lhs, rhs, "and")?,
            Operation::BitOr => llvm.builder.build_or(lhs, rhs, "or")?,
            Operation::Xor => llvm.builder.build_xor(lhs, rhs, "xor")?,
            _ => unreachable!(),
        })
    }

    fn emit_shift(&self, op: &Operation, srcs: &[usize]) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx;
        let val = self.state.load_int(srcs[0])?;
        let amt = self.state.load_int(srcs[1])?;
        let amt = if amt.get_type().get_bit_width() < val.get_type().get_bit_width() {
            llvm.builder
                .build_int_z_extend(amt, val.get_type(), "shl_ext")?
        } else {
            amt
        };
        Ok(if matches!(op, Operation::Shl) {
            llvm.builder.build_left_shift(val, amt, "shl")?
        } else {
            llvm.builder.build_right_shift(val, amt, false, "shr")?
        })
    }

    fn emit_logical_binop(&self, op: &Operation, srcs: &[usize]) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx;
        let lhs = self.state.load_int(srcs[0])?;
        let rhs = self.state.load_int(srcs[1])?;
        Ok(if matches!(op, Operation::And) {
            llvm.builder.build_and(lhs, rhs, "land")?
        } else {
            llvm.builder.build_or(lhs, rhs, "lor")?
        })
    }

    fn emit_not(&self, srcs: &[usize]) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx;
        let src = self.state.load_int(srcs[0])?;
        let one = llvm.i8_type.const_int(1, false);
        Ok(llvm.builder.build_xor(src, one, "not")?)
    }

    fn lower_cast(&self, src: usize, target_ty: IntType<'ctx>) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx;
        let val = self.state.load_int(src)?;
        let src_bits = val.get_type().get_bit_width();
        let dst_bits = target_ty.get_bit_width();
        Ok(if src_bits > dst_bits {
            llvm.builder.build_int_truncate(val, target_ty, "cast")?
        } else if src_bits < dst_bits {
            llvm.builder.build_int_z_extend(val, target_ty, "cast")?
        } else {
            val
        })
    }
}
