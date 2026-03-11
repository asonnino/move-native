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
    use move_binary_format::file_format::{Bytecode, SignatureToken};

    use crate::compiler::Compiler;
    use crate::module::CompiledModuleBuilder;
    use crate::target::Target;

    /// Build a module with `op(a: T, b: T): T { a <op> b }`.
    fn binary_operation_module(name: &str, ty: SignatureToken, op: Bytecode) -> String {
        let module = CompiledModuleBuilder::new()
            .function(
                name,
                vec![ty.clone(), ty.clone()],
                vec![ty],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::CopyLoc(1),
                    op,
                    Bytecode::Ret,
                ],
            )
            .build();
        Compiler::compile_module(&Target::Aarch64, &module)
            .unwrap()
            .to_string()
    }

    #[test]
    fn add_u64() {
        let asm = binary_operation_module("add_fn", SignatureToken::U64, Bytecode::Add);
        assert!(asm.contains("add_fn"), "missing symbol\n{asm}");
        assert!(asm.contains("\tadd\t"), "missing add instruction\n{asm}");
    }

    #[test]
    fn sub_u64() {
        let asm = binary_operation_module("sub_fn", SignatureToken::U64, Bytecode::Sub);
        assert!(
            asm.contains("\tsub\t") || asm.contains("\tsubs\t"),
            "missing sub instruction\n{asm}"
        );
    }

    #[test]
    fn mul_u64() {
        let asm = binary_operation_module("mul_fn", SignatureToken::U64, Bytecode::Mul);
        assert!(asm.contains("\tmul\t"), "missing mul instruction\n{asm}");
    }

    #[test]
    fn div_unsigned() {
        let asm = binary_operation_module("div_fn", SignatureToken::U64, Bytecode::Div);
        assert!(asm.contains("\tudiv\t"), "missing udiv instruction\n{asm}");
    }

    #[test]
    fn mod_unsigned() {
        let asm = binary_operation_module("mod_fn", SignatureToken::U64, Bytecode::Mod);
        // ARM64 computes mod as: x - (x / y) * y, using udiv + msub
        assert!(asm.contains("\tudiv\t"), "missing udiv for mod\n{asm}");
        assert!(asm.contains("\tmsub\t"), "missing msub for mod\n{asm}");
    }

    #[test]
    fn shift_left() {
        let asm = binary_operation_module("shl_fn", SignatureToken::U64, Bytecode::Shl);
        assert!(asm.contains("\tlsl\t"), "missing lsl instruction\n{asm}");
    }

    #[test]
    fn shift_right() {
        let asm = binary_operation_module("shr_fn", SignatureToken::U64, Bytecode::Shr);
        assert!(asm.contains("\tlsr\t"), "missing lsr instruction\n{asm}");
    }

    #[test]
    fn bitwise_and() {
        let asm = binary_operation_module("band_fn", SignatureToken::U64, Bytecode::BitAnd);
        assert!(asm.contains("\tand\t"), "missing and instruction\n{asm}");
    }

    #[test]
    fn bitwise_or() {
        let asm = binary_operation_module("bor_fn", SignatureToken::U64, Bytecode::BitOr);
        assert!(asm.contains("\torr\t"), "missing orr instruction\n{asm}");
    }

    #[test]
    fn bitwise_xor() {
        let asm = binary_operation_module("xor_fn", SignatureToken::U64, Bytecode::Xor);
        assert!(asm.contains("\teor\t"), "missing eor instruction\n{asm}");
    }

    #[test]
    fn comparison_lt() {
        let module = CompiledModuleBuilder::new()
            .function(
                "lt_fn",
                vec![SignatureToken::U64, SignatureToken::U64],
                vec![SignatureToken::Bool],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::CopyLoc(1),
                    Bytecode::Lt,
                    Bytecode::Ret,
                ],
            )
            .build();
        let asm = Compiler::compile_module(&Target::Aarch64, &module)
            .unwrap()
            .to_string();
        assert!(asm.contains("\tcmp\t"), "missing cmp instruction\n{asm}");
        assert!(asm.contains("\tcset\t"), "missing cset instruction\n{asm}");
    }

    #[test]
    fn cast_truncate() {
        let module = CompiledModuleBuilder::new()
            .function(
                "trunc_fn",
                vec![SignatureToken::U64],
                vec![SignatureToken::U8],
                vec![],
                vec![Bytecode::CopyLoc(0), Bytecode::CastU8, Bytecode::Ret],
            )
            .build();
        let asm = Compiler::compile_module(&Target::Aarch64, &module)
            .unwrap()
            .to_string();
        assert!(asm.contains("trunc_fn"), "missing symbol\n{asm}");
    }

    #[test]
    fn cast_extend() {
        let module = CompiledModuleBuilder::new()
            .function(
                "extend_fn",
                vec![SignatureToken::U8],
                vec![SignatureToken::U64],
                vec![],
                vec![Bytecode::CopyLoc(0), Bytecode::CastU64, Bytecode::Ret],
            )
            .build();
        let asm = Compiler::compile_module(&Target::Aarch64, &module)
            .unwrap()
            .to_string();
        assert!(asm.contains("extend_fn"), "missing symbol\n{asm}");
    }
}
