// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::IntPredicate;
use inkwell::types::IntType;
use inkwell::values::{BasicValueEnum, IntValue, StructValue};
use move_model::ty::{PrimitiveType, Type};
use move_stackless_bytecode::stackless_bytecode::Operation;

use super::state::{CallSiteValueExt, FunctionState};
use crate::context::DatatypeEnv;
use crate::error::{CompileError, CompileResult, to_field_index};
use crate::layout::EnumLayout;

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
            Operation::CastU8 => {
                self.lower_cast(self.state.source(sources, 0)?, self.state.ctx().i8_type)?
            }
            Operation::CastU16 => {
                self.lower_cast(self.state.source(sources, 0)?, self.state.ctx().i16_type)?
            }
            Operation::CastU32 => {
                self.lower_cast(self.state.source(sources, 0)?, self.state.ctx().i32_type)?
            }
            Operation::CastU64 => {
                self.lower_cast(self.state.source(sources, 0)?, self.state.ctx().i64_type)?
            }
            Operation::CastU128 => {
                self.lower_cast(self.state.source(sources, 0)?, self.state.ctx().i128_type)?
            }
            Operation::CastU256 => {
                self.lower_cast(self.state.source(sources, 0)?, self.state.ctx().i256_type)?
            }

            _ => unreachable!("ArithmeticEmitter::emit called with non-arithmetic op"),
        };
        self.state
            .store(self.state.destination(destinations, 0)?, result.into())?;
        Ok(())
    }

    /// Emit a conditional abort: if `condition` is true, call `__move_rt_arithmetic_error()`
    /// and mark the block unreachable; otherwise continue in a fresh basic block.
    fn emit_abort_if(&self, condition: IntValue<'ctx>) -> CompileResult<()> {
        let llvm = self.state.ctx();
        let current_block = llvm
            .builder
            .get_insert_block()
            .expect("builder has no insert block during function compilation");
        let function = current_block
            .get_parent()
            .expect("basic block has no parent function");
        let abort_block = llvm.context.append_basic_block(function, "abort");
        let continue_block = llvm.context.append_basic_block(function, "continue");

        llvm.builder
            .build_conditional_branch(condition, abort_block, continue_block)?;

        llvm.builder.position_at_end(abort_block);
        let abort_function = self.state.declare_external(
            "__move_rt_arithmetic_error",
            llvm.context.void_type().fn_type(&[], false),
        );
        llvm.builder
            .build_call(abort_function, &[], "arithmetic_error")?;
        llvm.builder.build_unreachable()?;

        llvm.builder.position_at_end(continue_block);
        Ok(())
    }

    fn emit_arithmetic(
        &self,
        operation: &Operation,
        sources: &[usize],
    ) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx();
        let lhs = self.state.load_int(self.state.source(sources, 0)?)?;
        let rhs = self.state.load_int(self.state.source(sources, 1)?)?;
        match operation {
            Operation::Add => {
                let result = llvm.builder.build_int_add(lhs, rhs, "add")?;
                let overflow =
                    llvm.builder
                        .build_int_compare(IntPredicate::ULT, result, lhs, "add_ov")?;
                self.emit_abort_if(overflow)?;
                Ok(result)
            }
            Operation::Sub => {
                let underflow =
                    llvm.builder
                        .build_int_compare(IntPredicate::ULT, lhs, rhs, "sub_uf")?;
                self.emit_abort_if(underflow)?;
                Ok(llvm.builder.build_int_sub(lhs, rhs, "sub")?)
            }
            Operation::Mul => {
                let result = llvm.builder.build_int_mul(lhs, rhs, "mul")?;
                let zero = rhs.get_type().const_int(0, false);
                let one = rhs.get_type().const_int(1, false);
                let rhs_nonzero =
                    llvm.builder
                        .build_int_compare(IntPredicate::NE, rhs, zero, "rhs_nz")?;
                let safe_divisor = llvm
                    .builder
                    .build_select(rhs_nonzero, rhs, one, "safe_div")?
                    .into_int_value();
                let div_back =
                    llvm.builder
                        .build_int_unsigned_div(result, safe_divisor, "div_back")?;
                let mismatch =
                    llvm.builder
                        .build_int_compare(IntPredicate::NE, div_back, lhs, "mul_mm")?;
                let overflow = llvm.builder.build_and(rhs_nonzero, mismatch, "mul_ov")?;
                self.emit_abort_if(overflow)?;
                Ok(result)
            }
            Operation::Div => {
                let zero = rhs.get_type().const_int(0, false);
                let is_zero =
                    llvm.builder
                        .build_int_compare(IntPredicate::EQ, rhs, zero, "div_z")?;
                self.emit_abort_if(is_zero)?;
                Ok(llvm.builder.build_int_unsigned_div(lhs, rhs, "div")?)
            }
            Operation::Mod => {
                let zero = rhs.get_type().const_int(0, false);
                let is_zero =
                    llvm.builder
                        .build_int_compare(IntPredicate::EQ, rhs, zero, "mod_z")?;
                self.emit_abort_if(is_zero)?;
                Ok(llvm.builder.build_int_unsigned_rem(lhs, rhs, "mod")?)
            }
            _ => unreachable!("emit_arithmetic called with non-arithmetic op"),
        }
    }

    fn emit_ord_cmp(
        &self,
        operation: &Operation,
        sources: &[usize],
    ) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx();
        let lhs = self.state.load_int(self.state.source(sources, 0)?)?;
        let rhs = self.state.load_int(self.state.source(sources, 1)?)?;
        let pred = match operation {
            Operation::Lt => IntPredicate::ULT,
            Operation::Gt => IntPredicate::UGT,
            Operation::Le => IntPredicate::ULE,
            Operation::Ge => IntPredicate::UGE,
            _ => unreachable!("emit_ord_cmp called with non-comparison op"),
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
        let llvm = self.state.ctx();
        let src0 = self.state.source(sources, 0)?;
        let src1 = self.state.source(sources, 1)?;
        let lhs = self.state.load_value(src0)?;
        let rhs = self.state.load_value(src1)?;
        let mty = self.state.get_local(src0)?.mty.clone();
        let eq = self.emit_eq_values(lhs, rhs, &mty)?;
        let result = if matches!(operation, Operation::Neq) {
            let one = llvm.i8_type.const_int(1, false);
            llvm.builder.build_xor(eq, one, "neq")?
        } else {
            eq
        };
        Ok(result)
    }

    /// Recursively compare two values for equality based on their Move type.
    /// Returns an i8 value: 1 for equal, 0 for not equal.
    fn emit_eq_values(
        &self,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
        mty: &Type,
    ) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx();
        match mty {
            // Integer-like types: direct int compare
            Type::Primitive(
                PrimitiveType::Bool
                | PrimitiveType::U8
                | PrimitiveType::U16
                | PrimitiveType::U32
                | PrimitiveType::U64
                | PrimitiveType::U128
                | PrimitiveType::U256
                | PrimitiveType::Address
                | PrimitiveType::Signer,
            ) => {
                let lhs = lhs.into_int_value();
                let rhs = rhs.into_int_value();
                let cmp = llvm
                    .builder
                    .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq")?;
                Ok(llvm
                    .builder
                    .build_int_z_extend(cmp, llvm.i8_type, "eq_ext")?)
            }

            // References: dereference both pointers, then compare the inner type
            Type::Reference(_, inner) => {
                let lhs_ptr = lhs.into_pointer_value();
                let rhs_ptr = rhs.into_pointer_value();
                let pointee_ty = self.state.lower_type(inner)?;
                let lhs_val = llvm.builder.build_load(pointee_ty, lhs_ptr, "deref_l")?;
                let rhs_val = llvm.builder.build_load(pointee_ty, rhs_ptr, "deref_r")?;
                self.emit_eq_values(lhs_val, rhs_val, inner)
            }

            // Vectors: opaque pointers, delegate to runtime
            Type::Vector(_) => {
                let lhs_ptr = lhs.into_pointer_value();
                let rhs_ptr = rhs.into_pointer_value();
                let fn_type = llvm
                    .i8_type
                    .fn_type(&[llvm.ptr_type.into(), llvm.ptr_type.into()], false);
                let func = self.state.declare_external("__move_rt_vec_eq", fn_type);
                let result =
                    llvm.builder
                        .build_call(func, &[lhs_ptr.into(), rhs_ptr.into()], "vec_eq")?;
                Ok(result.into_basic_value()?.into_int_value())
            }

            // Structs: field-by-field comparison, AND-reduce
            Type::Datatype(module_id, datatype_id, type_args) => {
                let lhs_struct = lhs.into_struct_value();
                let rhs_struct = rhs.into_struct_value();
                match llvm.get_datatype_env(*module_id, *datatype_id)? {
                    DatatypeEnv::Struct(struct_env) => {
                        let fields: Vec<Type> = struct_env
                            .get_fields()
                            .map(|f| {
                                let t = f.get_type();
                                if type_args.is_empty() {
                                    t
                                } else {
                                    t.instantiate(type_args)
                                }
                            })
                            .collect();
                        self.compare_struct_fields(lhs_struct, rhs_struct, &fields)
                    }
                    DatatypeEnv::Enum(enum_env) => {
                        let layout = EnumLayout::new(enum_env);
                        self.compare_enum_values(lhs_struct, rhs_struct, &layout, type_args)
                    }
                }
            }

            other => Err(CompileError::not_implemented(other)),
        }
    }

    fn compare_struct_fields(
        &self,
        lhs_struct: StructValue<'ctx>,
        rhs_struct: StructValue<'ctx>,
        field_types: &[Type],
    ) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx();
        let mut acc = llvm.i8_type.const_int(1, false);
        for (i, field_ty) in field_types.iter().enumerate() {
            let lhs_field = llvm.builder.build_extract_value(
                lhs_struct,
                to_field_index(i)?,
                &format!("l_{i}"),
            )?;
            let rhs_field = llvm.builder.build_extract_value(
                rhs_struct,
                to_field_index(i)?,
                &format!("r_{i}"),
            )?;
            let field_eq = self.emit_eq_values(lhs_field, rhs_field, field_ty)?;
            acc = llvm.builder.build_and(acc, field_eq, "and_eq")?;
        }
        Ok(acc)
    }

    /// Compare two enum values for equality.
    ///
    /// Correctness relies on `PackVariant` zero-initializing the enum struct
    /// (`const_zero()`) before setting only the active payload. Inactive variant
    /// slots are therefore zero on both sides and compare equal, so we can
    /// simply AND tag equality with all payload comparisons without masking by
    /// the active variant.
    fn compare_enum_values(
        &self,
        lhs_struct: StructValue<'ctx>,
        rhs_struct: StructValue<'ctx>,
        layout: &EnumLayout<'b>,
        type_args: &[Type],
    ) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx();

        debug_assert!(
            layout.variants().count() > 0,
            "enum with no variants should not reach equality comparison"
        );

        let lhs_tag = llvm
            .builder
            .build_extract_value(lhs_struct, 0, "lhs_enum_tag")?
            .into_int_value();
        let rhs_tag = llvm
            .builder
            .build_extract_value(rhs_struct, 0, "rhs_enum_tag")?
            .into_int_value();
        let tag_eq =
            llvm.builder
                .build_int_compare(IntPredicate::EQ, lhs_tag, rhs_tag, "enum_tag_eq")?;
        let mut acc = llvm
            .builder
            .build_int_z_extend(tag_eq, llvm.i8_type, "enum_tag_eq_i8")?;

        for variant in layout.variants() {
            let payload_types = variant.payload_field_types(type_args);
            let lhs_payload = llvm
                .builder
                .build_extract_value(lhs_struct, variant.payload_field_index()?, "lhs_payload")?
                .into_struct_value();
            let rhs_payload = llvm
                .builder
                .build_extract_value(rhs_struct, variant.payload_field_index()?, "rhs_payload")?
                .into_struct_value();
            let payload_eq =
                self.compare_struct_fields(lhs_payload, rhs_payload, &payload_types)?;
            acc = llvm.builder.build_and(acc, payload_eq, "enum_eq")?;
        }

        Ok(acc)
    }

    fn emit_bitwise(
        &self,
        operation: &Operation,
        sources: &[usize],
    ) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx();
        let lhs = self.state.load_int(self.state.source(sources, 0)?)?;
        let rhs = self.state.load_int(self.state.source(sources, 1)?)?;
        Ok(match operation {
            Operation::BitAnd => llvm.builder.build_and(lhs, rhs, "and")?,
            Operation::BitOr => llvm.builder.build_or(lhs, rhs, "or")?,
            Operation::Xor => llvm.builder.build_xor(lhs, rhs, "xor")?,
            _ => unreachable!("emit_bitwise called with non-bitwise op"),
        })
    }

    fn emit_shift(
        &self,
        operation: &Operation,
        sources: &[usize],
    ) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx();
        let val = self.state.load_int(self.state.source(sources, 0)?)?;
        let amt = self.state.load_int(self.state.source(sources, 1)?)?;
        let amt = if amt.get_type().get_bit_width() < val.get_type().get_bit_width() {
            llvm.builder
                .build_int_z_extend(amt, val.get_type(), "shl_ext")?
        } else if amt.get_type().get_bit_width() > val.get_type().get_bit_width() {
            return Err(CompileError::TypeMismatch(
                "shift amount wider than value".into(),
            ));
        } else {
            amt
        };

        let bit_width = val
            .get_type()
            .const_int(val.get_type().get_bit_width() as u64, false);
        let out_of_range =
            llvm.builder
                .build_int_compare(IntPredicate::UGE, amt, bit_width, "shr_oor")?;
        self.emit_abort_if(out_of_range)?;

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
        let llvm = self.state.ctx();
        let lhs = self.state.load_int(self.state.source(sources, 0)?)?;
        let rhs = self.state.load_int(self.state.source(sources, 1)?)?;
        Ok(if matches!(operation, Operation::And) {
            llvm.builder.build_and(lhs, rhs, "land")?
        } else {
            llvm.builder.build_or(lhs, rhs, "lor")?
        })
    }

    fn emit_not(&self, sources: &[usize]) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx();
        let source = self.state.load_int(self.state.source(sources, 0)?)?;
        let one = llvm.i8_type.const_int(1, false);
        Ok(llvm.builder.build_xor(source, one, "not")?)
    }

    fn lower_cast(&self, source: usize, target_ty: IntType<'ctx>) -> CompileResult<IntValue<'ctx>> {
        let llvm = self.state.ctx();
        let val = self.state.load_int(source)?;
        let source_bits = val.get_type().get_bit_width();
        let destination_bits = target_ty.get_bit_width();
        Ok(if source_bits > destination_bits {
            let shift_amt = val.get_type().const_int(destination_bits as u64, false);
            let high_bits = llvm
                .builder
                .build_right_shift(val, shift_amt, false, "hi")?;
            let zero = val.get_type().const_int(0, false);
            let overflow =
                llvm.builder
                    .build_int_compare(IntPredicate::NE, high_bits, zero, "cast_ov")?;
            self.emit_abort_if(overflow)?;
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
    use crate::Assembly;
    use crate::module::CompiledModuleBuilder;

    use move_binary_format::file_format::{Bytecode, DatatypeHandleIndex, SignatureToken};

    fn binary_op_asm(name: &str, ty: SignatureToken, op: Bytecode) -> Assembly {
        CompiledModuleBuilder::binary_op(name, ty, op).compile()
    }

    fn comparison_op_asm(name: &str, ty: SignatureToken, op: Bytecode) -> Assembly {
        CompiledModuleBuilder::comparison_op(name, ty, op).compile()
    }

    fn unary_op_asm(
        name: &str,
        input: SignatureToken,
        output: SignatureToken,
        op: Bytecode,
    ) -> Assembly {
        CompiledModuleBuilder::unary_op(name, input, output, op).compile()
    }

    #[test]
    fn add_u64() {
        let asm = binary_op_asm("add_fn", SignatureToken::U64, Bytecode::Add);
        assert!(asm.contains("0x0_M_add_fn"), "missing symbol\n{asm}");
        assert!(
            asm.contains("\tadd\t") || asm.contains("\tadds\t"),
            "missing add instruction\n{asm}"
        );
    }

    #[test]
    fn add_u256() {
        let asm = binary_op_asm("add_u256", SignatureToken::U256, Bytecode::Add);
        assert!(asm.contains("0x0_M_add_u256"), "missing symbol\n{asm}");
        // i256 add lowers to multi-word arithmetic with carry chain
        assert!(
            asm.contains("\tadds\t"),
            "missing adds (carry chain) for u256 add\n{asm}"
        );
    }

    #[test]
    fn sub_u64() {
        let asm = binary_op_asm("sub_fn", SignatureToken::U64, Bytecode::Sub);
        assert!(
            asm.contains("\tsub\t") || asm.contains("\tsubs\t"),
            "missing sub instruction\n{asm}"
        );
    }

    #[test]
    fn mul_u64() {
        let asm = binary_op_asm("mul_fn", SignatureToken::U64, Bytecode::Mul);
        assert!(asm.contains("\tmul\t"), "missing mul instruction\n{asm}");
    }

    #[test]
    fn div_unsigned() {
        let asm = binary_op_asm("div_fn", SignatureToken::U64, Bytecode::Div);
        assert!(asm.contains("\tudiv\t"), "missing udiv instruction\n{asm}");
    }

    #[test]
    fn mod_unsigned() {
        let asm = binary_op_asm("mod_fn", SignatureToken::U64, Bytecode::Mod);
        // ARM64 computes mod as: x - (x / y) * y, using udiv + msub
        assert!(asm.contains("\tudiv\t"), "missing udiv for mod\n{asm}");
        assert!(asm.contains("\tmsub\t"), "missing msub for mod\n{asm}");
    }

    #[test]
    fn comparison_lt() {
        let asm = comparison_op_asm("lt_fn", SignatureToken::U64, Bytecode::Lt);
        assert!(asm.contains("\tcmp\t"), "missing cmp instruction\n{asm}");
        assert!(asm.contains("\tcset\t"), "missing cset instruction\n{asm}");
    }

    #[test]
    fn comparison_eq() {
        let asm = comparison_op_asm("eq_fn", SignatureToken::U64, Bytecode::Eq);
        assert!(asm.contains("\tcmp\t"), "missing cmp instruction\n{asm}");
        assert!(asm.contains("\tcset\t"), "missing cset instruction\n{asm}");
        assert!(asm.contains("eq"), "missing eq condition\n{asm}");
    }

    #[test]
    fn comparison_neq() {
        let asm = comparison_op_asm("neq_fn", SignatureToken::U64, Bytecode::Neq);
        assert!(asm.contains("\tcmp\t"), "missing cmp instruction\n{asm}");
        assert!(asm.contains("\tcset\t"), "missing cset instruction\n{asm}");
        assert!(asm.contains("ne"), "missing ne condition\n{asm}");
    }

    #[test]
    fn bitwise_and() {
        let asm = binary_op_asm("band_fn", SignatureToken::U64, Bytecode::BitAnd);
        assert!(asm.contains("\tand\t"), "missing and instruction\n{asm}");
    }

    #[test]
    fn bitwise_or() {
        let asm = binary_op_asm("bor_fn", SignatureToken::U64, Bytecode::BitOr);
        assert!(asm.contains("\torr\t"), "missing orr instruction\n{asm}");
    }

    #[test]
    fn bitwise_xor() {
        let asm = binary_op_asm("xor_fn", SignatureToken::U64, Bytecode::Xor);
        assert!(asm.contains("\teor\t"), "missing eor instruction\n{asm}");
    }

    #[test]
    fn shift_left() {
        // Move shifts have signature (T, u8) -> T, exercising the z_extend path
        let asm = CompiledModuleBuilder::new()
            .function(
                "shl_fn",
                vec![SignatureToken::U64, SignatureToken::U8],
                vec![SignatureToken::U64],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::CopyLoc(1),
                    Bytecode::Shl,
                    Bytecode::Ret,
                ],
            )
            .compile();
        assert!(asm.contains("\tlsl\t"), "missing lsl instruction\n{asm}");
    }

    #[test]
    fn shift_right() {
        // Move shifts have signature (T, u8) -> T, exercising the z_extend path
        let asm = CompiledModuleBuilder::new()
            .function(
                "shr_fn",
                vec![SignatureToken::U64, SignatureToken::U8],
                vec![SignatureToken::U64],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::CopyLoc(1),
                    Bytecode::Shr,
                    Bytecode::Ret,
                ],
            )
            .compile();
        assert!(asm.contains("\tlsr\t"), "missing lsr instruction\n{asm}");
    }

    #[test]
    fn logical_not() {
        let asm = unary_op_asm(
            "not_fn",
            SignatureToken::Bool,
            SignatureToken::Bool,
            Bytecode::Not,
        );
        assert!(asm.contains("0x0_M_not_fn"), "missing symbol\n{asm}");
        assert!(asm.contains("\teor\t"), "missing eor instruction\n{asm}");
    }

    #[test]
    fn cast_truncate() {
        let asm = unary_op_asm(
            "trunc_fn",
            SignatureToken::U64,
            SignatureToken::U8,
            Bytecode::CastU8,
        );
        assert!(asm.contains("0x0_M_trunc_fn"), "missing symbol\n{asm}");
    }

    #[test]
    fn cast_extend() {
        let asm = unary_op_asm(
            "extend_fn",
            SignatureToken::U8,
            SignatureToken::U64,
            Bytecode::CastU64,
        );
        assert!(asm.contains("0x0_M_extend_fn"), "missing symbol\n{asm}");
    }

    #[test]
    fn cast_same_width_noop() {
        let asm = unary_op_asm(
            "cast_noop",
            SignatureToken::U64,
            SignatureToken::U64,
            Bytecode::CastU64,
        );
        assert!(asm.contains("0x0_M_cast_noop"), "missing symbol\n{asm}");
    }

    #[test]
    fn eq_ref_u64() {
        let ref_u64 = SignatureToken::Reference(Box::new(SignatureToken::U64));
        let asm = comparison_op_asm("eq_ref_u64", ref_u64, Bytecode::Eq);
        assert!(asm.contains("0x0_M_eq_ref_u64"), "missing symbol\n{asm}");
        // Should dereference (ldr) and then compare (cmp + cset)
        assert!(asm.contains("\tldr\t"), "missing ldr (deref)\n{asm}");
        assert!(asm.contains("\tcmp\t"), "missing cmp instruction\n{asm}");
    }

    #[test]
    fn neq_ref_u64() {
        let ref_u64 = SignatureToken::Reference(Box::new(SignatureToken::U64));
        let asm = comparison_op_asm("neq_ref_u64", ref_u64, Bytecode::Neq);
        assert!(asm.contains("0x0_M_neq_ref_u64"), "missing symbol\n{asm}");
        assert!(asm.contains("\tldr\t"), "missing ldr (deref)\n{asm}");
        // LLVM may optimize xor+zext into cset ne
        assert!(
            asm.contains("\teor\t") || asm.contains("ne"),
            "missing negation path\n{asm}"
        );
    }

    #[test]
    fn eq_vector_u8() {
        let vec_u8 = SignatureToken::Vector(Box::new(SignatureToken::U8));
        let asm = comparison_op_asm("eq_vec_u8", vec_u8, Bytecode::Eq);
        assert!(asm.contains("0x0_M_eq_vec_u8"), "missing symbol\n{asm}");
        assert!(
            asm.contains("__move_rt_vec_eq"),
            "missing __move_rt_vec_eq call\n{asm}"
        );
    }

    #[test]
    fn eq_ref_vector_u8() {
        let ref_vec_u8 = SignatureToken::Reference(Box::new(SignatureToken::Vector(Box::new(
            SignatureToken::U8,
        ))));
        let asm = comparison_op_asm("eq_ref_vec", ref_vec_u8, Bytecode::Eq);
        assert!(asm.contains("0x0_M_eq_ref_vec"), "missing symbol\n{asm}");
        // Should deref the reference, then call vec_eq
        assert!(asm.contains("\tldr\t"), "missing ldr (deref)\n{asm}");
        assert!(
            asm.contains("__move_rt_vec_eq"),
            "missing __move_rt_vec_eq call\n{asm}"
        );
    }

    #[test]
    fn eq_struct() {
        use move_binary_format::file_format::{AbilitySet, DatatypeHandleIndex};

        let asm = CompiledModuleBuilder::new()
            .struct_definition(
                "Point",
                AbilitySet::EMPTY
                    | move_binary_format::file_format::Ability::Copy
                    | move_binary_format::file_format::Ability::Drop,
                vec![("x", SignatureToken::U64), ("y", SignatureToken::U64)],
            )
            .function(
                "eq_point",
                vec![
                    SignatureToken::Datatype(DatatypeHandleIndex(0)),
                    SignatureToken::Datatype(DatatypeHandleIndex(0)),
                ],
                vec![SignatureToken::Bool],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::CopyLoc(1),
                    Bytecode::Eq,
                    Bytecode::Ret,
                ],
            )
            .compile();
        assert!(asm.contains("0x0_M_eq_point"), "missing symbol\n{asm}");
        // Field-by-field comparison: at least one cmp (LLVM may fuse/optimize)
        assert!(asm.contains("\tcmp\t"), "missing cmp instruction\n{asm}");
    }

    #[test]
    fn div_zero_emits_abort() {
        let asm = binary_op_asm("div_z", SignatureToken::U64, Bytecode::Div);
        assert!(
            asm.contains("__move_rt_arithmetic_error"),
            "div should emit arithmetic_error for zero check\n{asm}"
        );
    }

    #[test]
    fn add_overflow_emits_abort() {
        let asm = binary_op_asm("add_ov", SignatureToken::U64, Bytecode::Add);
        assert!(
            asm.contains("__move_rt_arithmetic_error"),
            "add should emit arithmetic_error for overflow check\n{asm}"
        );
    }

    #[test]
    fn sub_underflow_emits_abort() {
        let asm = binary_op_asm("sub_uf", SignatureToken::U64, Bytecode::Sub);
        assert!(
            asm.contains("__move_rt_arithmetic_error"),
            "sub should emit arithmetic_error for underflow check\n{asm}"
        );
    }

    #[test]
    fn mul_overflow_emits_abort() {
        let asm = binary_op_asm("mul_ov", SignatureToken::U64, Bytecode::Mul);
        assert!(
            asm.contains("__move_rt_arithmetic_error"),
            "mul should emit arithmetic_error for overflow check\n{asm}"
        );
    }

    #[test]
    fn shift_range_emits_abort() {
        let asm = CompiledModuleBuilder::new()
            .function(
                "shl_chk",
                vec![SignatureToken::U64, SignatureToken::U8],
                vec![SignatureToken::U64],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::CopyLoc(1),
                    Bytecode::Shl,
                    Bytecode::Ret,
                ],
            )
            .compile();
        assert!(
            asm.contains("__move_rt_arithmetic_error"),
            "shift should emit arithmetic_error for range check\n{asm}"
        );
    }

    #[test]
    fn cast_narrowing_emits_abort() {
        let asm = unary_op_asm(
            "trunc_chk",
            SignatureToken::U64,
            SignatureToken::U8,
            Bytecode::CastU8,
        );
        assert!(
            asm.contains("__move_rt_arithmetic_error"),
            "narrowing cast should emit arithmetic_error for overflow check\n{asm}"
        );
    }

    #[test]
    fn cast_widening_no_abort() {
        let asm = unary_op_asm(
            "widen_ok",
            SignatureToken::U8,
            SignatureToken::U64,
            Bytecode::CastU64,
        );
        assert!(
            !asm.contains("__move_rt_arithmetic_error"),
            "widening cast should NOT emit arithmetic_error\n{asm}"
        );
    }

    #[test]
    fn mod_zero_emits_abort() {
        let asm = binary_op_asm("mod_z", SignatureToken::U64, Bytecode::Mod);
        assert!(
            asm.contains("__move_rt_arithmetic_error"),
            "mod should emit arithmetic_error for zero check\n{asm}"
        );
    }

    #[test]
    fn logical_and() {
        let asm = binary_op_asm("and_fn", SignatureToken::Bool, Bytecode::And);
        assert!(asm.contains("0x0_M_and_fn"), "missing symbol\n{asm}");
    }

    #[test]
    fn logical_or() {
        let asm = binary_op_asm("or_fn", SignatureToken::Bool, Bytecode::Or);
        assert!(asm.contains("0x0_M_or_fn"), "missing symbol\n{asm}");
    }

    #[test]
    fn eq_enum() {
        let asm = CompiledModuleBuilder::option()
            .function(
                "eq_option",
                vec![
                    SignatureToken::Datatype(DatatypeHandleIndex(0)),
                    SignatureToken::Datatype(DatatypeHandleIndex(0)),
                ],
                vec![SignatureToken::Bool],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::CopyLoc(1),
                    Bytecode::Eq,
                    Bytecode::Ret,
                ],
            )
            .compile();
        assert!(asm.contains("0x0_M_eq_option"), "missing symbol\n{asm}");
        // Should compare tag and payload fields
        assert!(asm.contains("\tcmp\t"), "missing cmp instruction\n{asm}");
    }
}
