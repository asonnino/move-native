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
    pub(super) fn new(state: &'a FunctionState<'b, 'ctx>) -> Self {
        Self { state }
    }

    pub(super) fn emit(
        &self,
        destinations: &[usize],
        operation: &Operation,
        sources: &[usize],
    ) -> CompileResult<()> {
        let result = match operation {
            // Arithmetic: two same-type integers -> same type
            Operation::Add | Operation::Sub | Operation::Mul | Operation::Div | Operation::Mod => {
                self.emit_arithmetic(operation, sources)?
            }

            // Comparisons: two same-type integers -> bool (i8)
            Operation::Lt | Operation::Gt | Operation::Le | Operation::Ge => {
                self.emit_ord_cmp(operation, sources)?
            }
            Operation::Eq | Operation::Neq => self.emit_eq_cmp(operation, sources)?,

            // Bitwise: two same-type integers -> same type
            Operation::BitAnd | Operation::BitOr | Operation::Xor => {
                self.emit_bitwise(operation, sources)?
            }

            // Shifts: value (any width) + shift amount (u8) -> same type as value
            Operation::Shl | Operation::Shr => self.emit_shift(operation, sources)?,

            // Logical AND/OR: two bools (i8) -> bool (i8)
            Operation::And | Operation::Or => self.emit_logical_binop(operation, sources)?,

            // Logical NOT: bool (i8) -> bool (i8), implemented as XOR with 1
            Operation::Not => self.emit_not(sources)?,

            // Integer casts
            Operation::CastU8 => self.lower_cast(sources[0], self.state.ctx.i8_type)?,
            Operation::CastU16 => self.lower_cast(sources[0], self.state.ctx.i16_type)?,
            Operation::CastU32 => self.lower_cast(sources[0], self.state.ctx.i32_type)?,
            Operation::CastU64 => self.lower_cast(sources[0], self.state.ctx.i64_type)?,
            Operation::CastU128 => self.lower_cast(sources[0], self.state.ctx.i128_type)?,
            Operation::CastU256 => self.lower_cast(sources[0], self.state.ctx.i256_type)?,

            _ => unreachable!("ArithmeticEmitter::emit called with non-arithmetic op"),
        };
        self.state.store(destinations[0], result.into())?;
        Ok(())
    }

    fn emit_arithmetic(
        &self,
        operation: &Operation,
        sources: &[usize],
    ) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx;
        let lhs = self.state.load_int(sources[0])?;
        let rhs = self.state.load_int(sources[1])?;
        Ok(match operation {
            Operation::Add => llvm.builder.build_int_add(lhs, rhs, "add")?,
            Operation::Sub => llvm.builder.build_int_sub(lhs, rhs, "sub")?,
            Operation::Mul => llvm.builder.build_int_mul(lhs, rhs, "mul")?,
            Operation::Div => llvm.builder.build_int_unsigned_div(lhs, rhs, "div")?,
            Operation::Mod => llvm.builder.build_int_unsigned_rem(lhs, rhs, "mod")?,
            _ => unreachable!(),
        })
    }

    fn emit_ord_cmp(
        &self,
        operation: &Operation,
        sources: &[usize],
    ) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx;
        let lhs = self.state.load_int(sources[0])?;
        let rhs = self.state.load_int(sources[1])?;
        let pred = match operation {
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

    fn emit_eq_cmp(
        &self,
        operation: &Operation,
        sources: &[usize],
    ) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx;
        let lhs = self.state.load_int(sources[0])?;
        let rhs = self.state.load_int(sources[1])?;
        let pred = if matches!(operation, Operation::Eq) {
            IntPredicate::EQ
        } else {
            IntPredicate::NE
        };
        let cmp = llvm.builder.build_int_compare(pred, lhs, rhs, "cmp")?;
        Ok(llvm
            .builder
            .build_int_z_extend(cmp, llvm.i8_type, "cmp_ext")?)
    }

    fn emit_bitwise(
        &self,
        operation: &Operation,
        sources: &[usize],
    ) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx;
        let lhs = self.state.load_int(sources[0])?;
        let rhs = self.state.load_int(sources[1])?;
        Ok(match operation {
            Operation::BitAnd => llvm.builder.build_and(lhs, rhs, "and")?,
            Operation::BitOr => llvm.builder.build_or(lhs, rhs, "or")?,
            Operation::Xor => llvm.builder.build_xor(lhs, rhs, "xor")?,
            _ => unreachable!(),
        })
    }

    fn emit_shift(
        &self,
        operation: &Operation,
        sources: &[usize],
    ) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx;
        let val = self.state.load_int(sources[0])?;
        let amt = self.state.load_int(sources[1])?;
        let amt = if amt.get_type().get_bit_width() < val.get_type().get_bit_width() {
            llvm.builder
                .build_int_z_extend(amt, val.get_type(), "shl_ext")?
        } else {
            amt
        };
        Ok(if matches!(operation, Operation::Shl) {
            llvm.builder.build_left_shift(val, amt, "shl")?
        } else {
            llvm.builder.build_right_shift(val, amt, false, "shr")?
        })
    }

    fn emit_logical_binop(
        &self,
        operation: &Operation,
        sources: &[usize],
    ) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx;
        let lhs = self.state.load_int(sources[0])?;
        let rhs = self.state.load_int(sources[1])?;
        Ok(if matches!(operation, Operation::And) {
            llvm.builder.build_and(lhs, rhs, "land")?
        } else {
            llvm.builder.build_or(lhs, rhs, "lor")?
        })
    }

    fn emit_not(&self, sources: &[usize]) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx;
        let source = self.state.load_int(sources[0])?;
        let one = llvm.i8_type.const_int(1, false);
        Ok(llvm.builder.build_xor(source, one, "not")?)
    }

    fn lower_cast(&self, source: usize, target_ty: IntType<'ctx>) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx;
        let val = self.state.load_int(source)?;
        let source_bits = val.get_type().get_bit_width();
        let destination_bits = target_ty.get_bit_width();
        Ok(if source_bits > destination_bits {
            llvm.builder.build_int_truncate(val, target_ty, "cast")?
        } else if source_bits < destination_bits {
            llvm.builder.build_int_z_extend(val, target_ty, "cast")?
        } else {
            val
        })
    }
}

#[cfg(test)]
mod tests {
    use move_model::ty::{PrimitiveType, Type};
    use move_stackless_bytecode::stackless_bytecode::Operation;

    use super::super::state::FunctionState;
    use super::ArithmeticEmitter;
    use crate::context::LlvmContext;

    fn locals(p: PrimitiveType, n: usize) -> Vec<Type> {
        vec![Type::Primitive(p); n]
    }

    #[test]
    fn add_u64() {
        let llvm = LlvmContext::new_for_test();
        let state =
            FunctionState::new_for_test(&llvm, locals(PrimitiveType::U64, 3), vec![]).unwrap();
        ArithmeticEmitter::new(&state)
            .emit(&[2], &Operation::Add, &[0, 1])
            .unwrap();
        let ir = llvm.module.print_to_string().to_string();
        assert!(ir.contains("add i64"), "IR: {ir}");
    }

    #[test]
    fn sub_u32() {
        let llvm = LlvmContext::new_for_test();
        let state =
            FunctionState::new_for_test(&llvm, locals(PrimitiveType::U32, 3), vec![]).unwrap();
        ArithmeticEmitter::new(&state)
            .emit(&[2], &Operation::Sub, &[0, 1])
            .unwrap();
        let ir = llvm.module.print_to_string().to_string();
        assert!(ir.contains("sub i32"), "IR: {ir}");
    }

    #[test]
    fn mul_u8() {
        let llvm = LlvmContext::new_for_test();
        let state =
            FunctionState::new_for_test(&llvm, locals(PrimitiveType::U8, 3), vec![]).unwrap();
        ArithmeticEmitter::new(&state)
            .emit(&[2], &Operation::Mul, &[0, 1])
            .unwrap();
        let ir = llvm.module.print_to_string().to_string();
        assert!(ir.contains("mul i8"), "IR: {ir}");
    }

    #[test]
    fn div_unsigned() {
        let llvm = LlvmContext::new_for_test();
        let state =
            FunctionState::new_for_test(&llvm, locals(PrimitiveType::U64, 3), vec![]).unwrap();
        ArithmeticEmitter::new(&state)
            .emit(&[2], &Operation::Div, &[0, 1])
            .unwrap();
        let ir = llvm.module.print_to_string().to_string();
        assert!(ir.contains("udiv i64"), "IR: {ir}");
    }

    #[test]
    fn mod_unsigned() {
        let llvm = LlvmContext::new_for_test();
        let state =
            FunctionState::new_for_test(&llvm, locals(PrimitiveType::U64, 3), vec![]).unwrap();
        ArithmeticEmitter::new(&state)
            .emit(&[2], &Operation::Mod, &[0, 1])
            .unwrap();
        let ir = llvm.module.print_to_string().to_string();
        assert!(ir.contains("urem i64"), "IR: {ir}");
    }

    #[test]
    fn shift_same_width() {
        let llvm = LlvmContext::new_for_test();
        let state =
            FunctionState::new_for_test(&llvm, locals(PrimitiveType::U64, 3), vec![]).unwrap();
        ArithmeticEmitter::new(&state)
            .emit(&[2], &Operation::Shl, &[0, 1])
            .unwrap();
        let ir = llvm.module.print_to_string().to_string();
        assert!(ir.contains("shl i64"), "IR: {ir}");
        assert!(
            !ir.contains("zext"),
            "no zext expected when widths match: {ir}"
        );
    }

    #[test]
    fn shift_narrow_amount() {
        let llvm = LlvmContext::new_for_test();
        let types = vec![
            Type::Primitive(PrimitiveType::U64),
            Type::Primitive(PrimitiveType::U8),
            Type::Primitive(PrimitiveType::U64),
        ];
        let state = FunctionState::new_for_test(&llvm, types, vec![]).unwrap();
        ArithmeticEmitter::new(&state)
            .emit(&[2], &Operation::Shl, &[0, 1])
            .unwrap();
        let ir = llvm.module.print_to_string().to_string();
        assert!(ir.contains("zext i8"), "IR: {ir}");
    }

    #[test]
    fn cast_truncate() {
        let llvm = LlvmContext::new_for_test();
        let types = vec![
            Type::Primitive(PrimitiveType::U64),
            Type::Primitive(PrimitiveType::U8),
        ];
        let state = FunctionState::new_for_test(&llvm, types, vec![]).unwrap();
        ArithmeticEmitter::new(&state)
            .emit(&[1], &Operation::CastU8, &[0])
            .unwrap();
        let ir = llvm.module.print_to_string().to_string();
        assert!(ir.contains("trunc i64"), "IR: {ir}");
    }

    #[test]
    fn cast_extend() {
        let llvm = LlvmContext::new_for_test();
        let types = vec![
            Type::Primitive(PrimitiveType::U8),
            Type::Primitive(PrimitiveType::U64),
        ];
        let state = FunctionState::new_for_test(&llvm, types, vec![]).unwrap();
        ArithmeticEmitter::new(&state)
            .emit(&[1], &Operation::CastU64, &[0])
            .unwrap();
        let ir = llvm.module.print_to_string().to_string();
        assert!(ir.contains("zext i8"), "IR: {ir}");
    }

    #[test]
    fn comparison_produces_i8() {
        let llvm = LlvmContext::new_for_test();
        let types = vec![
            Type::Primitive(PrimitiveType::U64),
            Type::Primitive(PrimitiveType::U64),
            Type::Primitive(PrimitiveType::Bool),
        ];
        let state = FunctionState::new_for_test(&llvm, types, vec![]).unwrap();
        ArithmeticEmitter::new(&state)
            .emit(&[2], &Operation::Lt, &[0, 1])
            .unwrap();
        let ir = llvm.module.print_to_string().to_string();
        assert!(ir.contains("icmp ult"), "IR: {ir}");
        assert!(ir.contains("zext i1"), "IR: {ir}");
    }
}
