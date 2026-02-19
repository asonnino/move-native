// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;

use inkwell::IntPredicate;
use inkwell::basic_block::BasicBlock;
use inkwell::types::{BasicType, BasicTypeEnum, IntType};
use inkwell::values::{BasicValueEnum, FunctionValue, IntValue, PointerValue};
use move_model::model::FunctionEnv;
use move_model::ty::Type;
use move_stackless_bytecode::function_target::FunctionData;
use move_stackless_bytecode::stackless_bytecode::{
    AssignKind, Bytecode, Constant, Label, Operation,
};

use crate::context::LlvmContext;
use crate::error::CompileError;
use crate::types::lower_model_type;

/// A single local variable (param, local, or compiler-generated temp).
///
/// Bundles the Move type, LLVM type, and alloca pointer together so they
/// cannot get out of sync.
#[derive(Clone)]
struct Local<'ctx> {
    /// The Move-level type of this local.
    mty: Type,
    /// The lowered LLVM type (cached to avoid re-lowering on every load).
    llvm_ty: BasicTypeEnum<'ctx>,
    /// The alloca in the entry block that backs this local.
    alloca: PointerValue<'ctx>,
}

/// Per-function lowering state.
///
/// Uses the alloca/mem2reg pattern: each stackless bytecode temp is mapped to
/// an LLVM `alloca` in the entry block. LLVM's `mem2reg` pass later promotes
/// these to SSA registers.
struct FunctionLowering<'a, 'ctx> {
    ctx: &'a LlvmContext<'ctx>,
    /// The global model environment, for resolving callee functions.
    env: &'a move_model::model::GlobalEnv,
    /// All locals (params + locals + compiler-generated temps).
    locals: Vec<Local<'ctx>>,
    /// Pre-created basic blocks for each Label in the bytecode.
    label_blocks: BTreeMap<Label, BasicBlock<'ctx>>,
}

impl<'a, 'ctx> FunctionLowering<'a, 'ctx> {
    fn new(
        ctx: &'a LlvmContext<'ctx>,
        env: &'a move_model::model::GlobalEnv,
        function: FunctionValue<'ctx>,
        param_count: usize,
        func_data: &FunctionData,
    ) -> Result<Self, CompileError> {
        let entry = ctx.context.append_basic_block(function, "entry");
        ctx.builder.position_at_end(entry);

        // Allocas for all locals
        let mut locals = Vec::with_capacity(func_data.local_types.len());
        for (i, mty) in func_data.local_types.iter().enumerate() {
            let llvm_ty = lower_model_type(ctx, env, mty)?;
            let alloca = ctx.builder.build_alloca(llvm_ty, &format!("t{i}")).unwrap();
            locals.push(Local {
                mty: mty.clone(),
                llvm_ty,
                alloca,
            });
        }

        // Store function parameters into their allocas
        for (i, local) in locals.iter().enumerate().take(param_count) {
            let param = function.get_nth_param(i as u32).unwrap();
            ctx.builder.build_store(local.alloca, param).unwrap();
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
            env,
            locals,
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
            Bytecode::Assign(_, dst, src, kind) => {
                // Move-swap optimization: for Move of struct types, swap the
                // local slots instead of load+store. Move guarantees the source
                // is dead after this point, so reusing its alloca is safe and
                // avoids an unnecessary copy.
                if matches!(kind, AssignKind::Move) && self.locals[*src].mty.is_struct() {
                    self.locals[*dst] = self.locals[*src].clone();
                } else {
                    let val = self.load_value(*src)?;
                    self.store(*dst, val);
                }
            }
            Bytecode::Load(_, dst, constant) => {
                let val = self.lower_constant(constant)?;
                self.store(*dst, val.into());
            }
            Bytecode::Call(_, dsts, op, srcs, _) => {
                self.lower_operation(dsts, op, srcs)?;
            }
            Bytecode::Ret(_, rets) => {
                if rets.is_empty() {
                    self.ctx.builder.build_return(None).unwrap();
                } else {
                    let val = self.load_value(rets[0])?;
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
                let cond_val = self.load_int(*cond)?;
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

    /// Load a local as a generic `BasicValueEnum` (works for any type).
    fn load_value(&self, idx: usize) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let local = &self.locals[idx];
        Ok(self
            .ctx
            .builder
            .build_load(local.llvm_ty, local.alloca, &format!("t{idx}"))
            .unwrap())
    }

    /// Load a local as an `IntValue` (convenience for arithmetic/comparison ops).
    fn load_int(&self, idx: usize) -> Result<IntValue<'ctx>, CompileError> {
        Ok(self.load_value(idx)?.into_int_value())
    }

    /// Store a value into a local's alloca.
    fn store(&self, idx: usize, val: BasicValueEnum<'ctx>) {
        self.ctx
            .builder
            .build_store(self.locals[idx].alloca, val)
            .unwrap();
    }

    /// Resolve the pointee LLVM type for a local that holds a reference (`&T` or `&mut T`).
    fn pointee_type(&self, idx: usize) -> Result<BasicTypeEnum<'ctx>, CompileError> {
        match &self.locals[idx].mty {
            Type::Reference(_, inner) => lower_model_type(self.ctx, self.env, inner),
            other => Err(CompileError::UnsupportedType(format!(
                "expected reference type, got {:?}",
                other
            ))),
        }
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
        let result = match op {
            // Arithmetic: two same-type integers → same type
            Operation::Add | Operation::Sub | Operation::Mul | Operation::Div | Operation::Mod => {
                let lhs = self.load_int(srcs[0])?;
                let rhs = self.load_int(srcs[1])?;
                match op {
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
                }
            }

            // Comparisons: two same-type integers → bool (i8)
            Operation::Lt | Operation::Gt | Operation::Le | Operation::Ge => {
                let lhs = self.load_int(srcs[0])?;
                let rhs = self.load_int(srcs[1])?;
                let pred = match op {
                    Operation::Lt => IntPredicate::ULT,
                    Operation::Gt => IntPredicate::UGT,
                    Operation::Le => IntPredicate::ULE,
                    Operation::Ge => IntPredicate::UGE,
                    _ => unreachable!(),
                };
                let cmp = self
                    .ctx
                    .builder
                    .build_int_compare(pred, lhs, rhs, "cmp")
                    .unwrap();
                self.ctx
                    .builder
                    .build_int_z_extend(cmp, self.ctx.i8_type, "cmp_ext")
                    .unwrap()
            }
            Operation::Eq | Operation::Neq => {
                let lhs = self.load_int(srcs[0])?;
                let rhs = self.load_int(srcs[1])?;
                let pred = if matches!(op, Operation::Eq) {
                    IntPredicate::EQ
                } else {
                    IntPredicate::NE
                };
                let cmp = self
                    .ctx
                    .builder
                    .build_int_compare(pred, lhs, rhs, "cmp")
                    .unwrap();
                self.ctx
                    .builder
                    .build_int_z_extend(cmp, self.ctx.i8_type, "cmp_ext")
                    .unwrap()
            }

            // Bitwise: two same-type integers → same type
            Operation::BitAnd => {
                let lhs = self.load_int(srcs[0])?;
                let rhs = self.load_int(srcs[1])?;
                self.ctx.builder.build_and(lhs, rhs, "and").unwrap()
            }
            Operation::BitOr => {
                let lhs = self.load_int(srcs[0])?;
                let rhs = self.load_int(srcs[1])?;
                self.ctx.builder.build_or(lhs, rhs, "or").unwrap()
            }
            Operation::Xor => {
                let lhs = self.load_int(srcs[0])?;
                let rhs = self.load_int(srcs[1])?;
                self.ctx.builder.build_xor(lhs, rhs, "xor").unwrap()
            }

            // Shifts: value (any width) + shift amount (u8) → same type as value
            Operation::Shl | Operation::Shr => {
                let val = self.load_int(srcs[0])?;
                let amt = self.load_int(srcs[1])?;
                let amt = if amt.get_type().get_bit_width() < val.get_type().get_bit_width() {
                    self.ctx
                        .builder
                        .build_int_z_extend(amt, val.get_type(), "shl_ext")
                        .unwrap()
                } else {
                    amt
                };
                if matches!(op, Operation::Shl) {
                    self.ctx.builder.build_left_shift(val, amt, "shl").unwrap()
                } else {
                    self.ctx
                        .builder
                        .build_right_shift(val, amt, false, "shr")
                        .unwrap()
                }
            }

            // Logical AND/OR: two bools (i8) → bool (i8)
            Operation::And => {
                let lhs = self.load_int(srcs[0])?;
                let rhs = self.load_int(srcs[1])?;
                self.ctx.builder.build_and(lhs, rhs, "land").unwrap()
            }
            Operation::Or => {
                let lhs = self.load_int(srcs[0])?;
                let rhs = self.load_int(srcs[1])?;
                self.ctx.builder.build_or(lhs, rhs, "lor").unwrap()
            }

            // Logical NOT: bool (i8) → bool (i8), implemented as XOR with 1
            Operation::Not => {
                let src = self.load_int(srcs[0])?;
                let one = self.ctx.i8_type.const_int(1, false);
                self.ctx.builder.build_xor(src, one, "not").unwrap()
            }

            // Integer casts
            Operation::CastU8 => self.lower_cast(srcs[0], self.ctx.i8_type)?,
            Operation::CastU16 => self.lower_cast(srcs[0], self.ctx.i16_type)?,
            Operation::CastU32 => self.lower_cast(srcs[0], self.ctx.i32_type)?,
            Operation::CastU64 => self.lower_cast(srcs[0], self.ctx.i64_type)?,
            Operation::CastU128 => self.lower_cast(srcs[0], self.ctx.i128_type)?,
            Operation::CastU256 => self.lower_cast(srcs[0], self.ctx.i256_type)?,

            // Function call: resolve callee and emit LLVM call
            Operation::Function(module_id, fun_id, type_args) => {
                if !type_args.is_empty() {
                    return Err(CompileError::UnsupportedOperation(
                        "generic function calls not yet supported".to_string(),
                    ));
                }
                let callee_env = self.env.get_module(*module_id).into_function(*fun_id);
                let callee_name = callee_env.get_name_str();
                let callee_fn = self.ctx.module.get_function(&callee_name).ok_or_else(|| {
                    CompileError::UnsupportedOperation(format!(
                        "callee not found (cross-module?): {callee_name}"
                    ))
                })?;

                let args: Vec<_> = srcs
                    .iter()
                    .map(|s| self.load_value(*s).map(|v| v.into()))
                    .collect::<Result<_, _>>()?;

                let call = self
                    .ctx
                    .builder
                    .build_call(callee_fn, &args, &callee_name)
                    .unwrap();

                if !dsts.is_empty() {
                    let ret_val = match call.try_as_basic_value() {
                        inkwell::values::ValueKind::Basic(v) => v,
                        _ => panic!("expected non-void return from callee"),
                    };
                    self.store(dsts[0], ret_val);
                }
                return Ok(());
            }

            // Pack: construct a struct from field values
            Operation::Pack(mid, did, type_args) => {
                if !type_args.is_empty() {
                    return Err(CompileError::UnsupportedOperation(
                        "generic Pack not yet supported".to_string(),
                    ));
                }
                let struct_ty =
                    lower_model_type(self.ctx, self.env, &Type::Datatype(*mid, *did, vec![]))?
                        .into_struct_type();
                let mut agg = struct_ty.get_undef();
                for (i, src) in srcs.iter().enumerate() {
                    let field_val = self.load_value(*src)?;
                    agg = self
                        .ctx
                        .builder
                        .build_insert_value(agg, field_val, i as u32, &format!("pack_{i}"))
                        .unwrap()
                        .into_struct_value();
                }
                self.store(dsts[0], agg.into());
                return Ok(());
            }

            // Unpack: destructure a struct into field values
            Operation::Unpack(mid, did, type_args) => {
                if !type_args.is_empty() {
                    return Err(CompileError::UnsupportedOperation(
                        "generic Unpack not yet supported".to_string(),
                    ));
                }
                let struct_val = self.load_value(srcs[0])?.into_struct_value();
                let struct_env = self.env.get_module(*mid).into_struct(*did);
                let field_count = struct_env.get_fields().count();
                for (i, dst) in dsts.iter().enumerate().take(field_count) {
                    let field_val = self
                        .ctx
                        .builder
                        .build_extract_value(struct_val, i as u32, &format!("unpack_{i}"))
                        .unwrap();
                    self.store(*dst, field_val);
                }
                return Ok(());
            }

            // BorrowLoc: take the address of a local → &T
            Operation::BorrowLoc => {
                // srcs[0] is the local index; we want its alloca address, not its value.
                let ptr = self.locals[srcs[0]].alloca;
                self.store(dsts[0], ptr.into());
                return Ok(());
            }

            // BorrowField: GEP into a struct through a reference → &Field
            Operation::BorrowField(mid, did, type_args, offset) => {
                if !type_args.is_empty() {
                    return Err(CompileError::UnsupportedOperation(
                        "generic BorrowField not yet supported".to_string(),
                    ));
                }
                let struct_ptr = self.load_value(srcs[0])?.into_pointer_value();
                let struct_ty =
                    lower_model_type(self.ctx, self.env, &Type::Datatype(*mid, *did, vec![]))?;
                let field_ptr = self
                    .ctx
                    .builder
                    .build_struct_gep(struct_ty, struct_ptr, *offset as u32, "borrow_field")
                    .unwrap();
                self.store(dsts[0], field_ptr.into());
                return Ok(());
            }

            // ReadRef: load through a reference → T
            Operation::ReadRef => {
                let ptr = self.load_value(srcs[0])?.into_pointer_value();
                let pointee_ty = self.pointee_type(srcs[0])?;
                let val = self
                    .ctx
                    .builder
                    .build_load(pointee_ty, ptr, "read_ref")
                    .unwrap();
                self.store(dsts[0], val);
                return Ok(());
            }

            // WriteRef: store through a mutable reference
            Operation::WriteRef => {
                let ptr = self.load_value(srcs[0])?.into_pointer_value();
                let val = self.load_value(srcs[1])?;
                self.ctx.builder.build_store(ptr, val).unwrap();
                return Ok(());
            }

            // FreezeRef: &mut T → &T (no-op, just copy the pointer)
            Operation::FreezeRef => {
                let ptr = self.load_value(srcs[0])?;
                self.store(dsts[0], ptr);
                return Ok(());
            }

            // GetField: extract a single field from a struct
            Operation::GetField(mid, did, type_args, offset) => {
                if !type_args.is_empty() {
                    return Err(CompileError::UnsupportedOperation(
                        "generic GetField not yet supported".to_string(),
                    ));
                }
                let _ = (mid, did); // used only for type_args check
                let struct_val = self.load_value(srcs[0])?.into_struct_value();
                let field_val = self
                    .ctx
                    .builder
                    .build_extract_value(struct_val, *offset as u32, "getfield")
                    .unwrap();
                self.store(dsts[0], field_val);
                return Ok(());
            }

            other => {
                return Err(CompileError::UnsupportedOperation(format!("{:?}", other)));
            }
        };
        self.store(dsts[0], result.into());
        Ok(())
    }

    fn lower_cast(
        &self,
        src: usize,
        target_ty: IntType<'ctx>,
    ) -> Result<IntValue<'ctx>, CompileError> {
        let val = self.load_int(src)?;
        let src_bits = val.get_type().get_bit_width();
        let dst_bits = target_ty.get_bit_width();
        Ok(if src_bits > dst_bits {
            self.ctx
                .builder
                .build_int_truncate(val, target_ty, "cast")
                .unwrap()
        } else if src_bits < dst_bits {
            self.ctx
                .builder
                .build_int_z_extend(val, target_ty, "cast")
                .unwrap()
        } else {
            val
        })
    }
}

/// Declare an LLVM function (signature only, no body) for the given Move function.
pub fn declare_function<'ctx>(
    ctx: &LlvmContext<'ctx>,
    env: &move_model::model::GlobalEnv,
    func_env: &FunctionEnv<'_>,
    func_data: &FunctionData,
) -> Result<FunctionValue<'ctx>, CompileError> {
    let name = func_env
        .module_env
        .env
        .symbol_pool()
        .string(func_env.get_name());
    let param_count = func_env.get_parameter_count();

    // Build LLVM parameter types
    let param_llvm_types: Vec<_> = func_data.local_types[..param_count]
        .iter()
        .map(|ty| lower_model_type(ctx, env, ty).map(|t| t.into()))
        .collect::<Result<_, _>>()?;

    // Build LLVM function type
    let fn_type = if func_data.return_types.is_empty() {
        ctx.context.void_type().fn_type(&param_llvm_types, false)
    } else if func_data.return_types.len() == 1 {
        let ret_type = lower_model_type(ctx, env, &func_data.return_types[0])?;
        ret_type.fn_type(&param_llvm_types, false)
    } else {
        return Err(CompileError::UnsupportedType(
            "multi-value return".to_string(),
        ));
    };

    Ok(ctx.module.add_function(&name, fn_type, None))
}

/// Compile the body of an already-declared LLVM function.
pub fn compile_function<'ctx>(
    ctx: &LlvmContext<'ctx>,
    env: &move_model::model::GlobalEnv,
    function: FunctionValue<'ctx>,
    func_env: &FunctionEnv<'_>,
    func_data: &FunctionData,
) -> Result<(), CompileError> {
    let param_count = func_env.get_parameter_count();
    let mut lowering = FunctionLowering::new(ctx, env, function, param_count, func_data)?;
    lowering.lower_code(func_data)?;
    Ok(())
}

/// Lower a single function into the LLVM module using stackless bytecode.
///
/// Convenience wrapper that declares and compiles in one step.
pub fn lower_function<'ctx>(
    ctx: &LlvmContext<'ctx>,
    env: &move_model::model::GlobalEnv,
    func_env: &FunctionEnv<'_>,
    func_data: &FunctionData,
) -> Result<(), CompileError> {
    let function = declare_function(ctx, env, func_env, func_data)?;
    compile_function(ctx, env, function, func_env, func_data)
}
