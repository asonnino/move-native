// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;

use inkwell::IntPredicate;
use inkwell::basic_block::BasicBlock;
use inkwell::module::Linkage;
use inkwell::types::{BasicType, BasicTypeEnum, IntType};
use inkwell::values::{BasicValueEnum, FunctionValue, IntValue, PointerValue};
use move_model::model::FunctionEnv;
use move_model::ty::Type;
use move_stackless_bytecode::function_target::FunctionData;
use move_stackless_bytecode::stackless_bytecode::{
    AssignKind, Bytecode, Constant, Label, Operation,
};
use move_stackless_bytecode::stackless_bytecode_generator::StacklessBytecodeGenerator;

use crate::context::LlvmContext;
use crate::error::CompileError;
use crate::mangle::{mangle_native_symbol, mangle_type, mangle_type_args};
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
    /// Concrete types for the function's type parameters (empty for non-generic).
    type_params: Vec<Type>,
    /// Counter for unique global constant names.
    const_counter: usize,
}

impl<'a, 'ctx> FunctionLowering<'a, 'ctx> {
    fn new(
        ctx: &'a LlvmContext<'ctx>,
        env: &'a move_model::model::GlobalEnv,
        function: FunctionValue<'ctx>,
        param_count: usize,
        func_data: &FunctionData,
        type_params: Vec<Type>,
    ) -> Result<Self, CompileError> {
        let entry = ctx.context.append_basic_block(function, "entry");
        ctx.builder.position_at_end(entry);

        // Allocas for all locals
        let mut locals = Vec::with_capacity(func_data.local_types.len());
        for (i, mty) in func_data.local_types.iter().enumerate() {
            let mty = if type_params.is_empty() {
                mty.clone()
            } else {
                mty.instantiate(&type_params)
            };
            let llvm_ty = lower_model_type(ctx, env, &mty)?;
            let alloca = ctx.builder.build_alloca(llvm_ty, &format!("t{i}")).unwrap();
            locals.push(Local {
                mty,
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
            type_params,
            const_counter: 0,
        })
    }

    /// Instantiate type_args through the current function's type parameters.
    /// Returns the args unchanged for non-generic functions.
    fn inst_types(&self, types: &[Type]) -> Vec<Type> {
        if self.type_params.is_empty() {
            types.to_vec()
        } else {
            types
                .iter()
                .map(|t| t.instantiate(&self.type_params))
                .collect()
        }
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
                self.store(*dst, val);
            }
            Bytecode::Call(_, dsts, op, srcs, _) => {
                self.lower_operation(dsts, op, srcs)?;
            }
            Bytecode::Ret(_, rets) => {
                if rets.is_empty() {
                    self.ctx.builder.build_return(None).unwrap();
                } else if rets.len() == 1 {
                    let val = self.load_value(rets[0])?;
                    self.ctx.builder.build_return(Some(&val)).unwrap();
                } else {
                    // Multi-return: pack values into an anonymous struct
                    let ret_types: Vec<BasicTypeEnum<'ctx>> = rets
                        .iter()
                        .map(|r| Ok(self.locals[*r].llvm_ty))
                        .collect::<Result<_, CompileError>>()?;
                    let ret_struct_ty = self.ctx.context.struct_type(&ret_types, false);
                    let mut agg = ret_struct_ty.get_undef();
                    for (i, r) in rets.iter().enumerate() {
                        let val = self.load_value(*r)?;
                        agg = self
                            .ctx
                            .builder
                            .build_insert_value(agg, val, i as u32, &format!("ret_{i}"))
                            .unwrap()
                            .into_struct_value();
                    }
                    self.ctx.builder.build_return(Some(&agg)).unwrap();
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
            Bytecode::Abort(_, code_idx) => {
                let code = self.load_value(*code_idx)?;
                let abort_fn = self.get_or_declare_abort_fn();
                self.ctx
                    .builder
                    .build_call(abort_fn, &[code.into()], "abort")
                    .unwrap();
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

    fn lower_constant(
        &mut self,
        constant: &Constant,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        match constant {
            Constant::Bool(v) => Ok(self.ctx.i8_type.const_int(*v as u64, false).into()),
            Constant::U8(v) => Ok(self.ctx.i8_type.const_int(*v as u64, false).into()),
            Constant::U16(v) => Ok(self.ctx.i16_type.const_int(*v as u64, false).into()),
            Constant::U32(v) => Ok(self.ctx.i32_type.const_int(*v as u64, false).into()),
            Constant::U64(v) => Ok(self.ctx.i64_type.const_int(*v, false).into()),
            Constant::U128(v) => {
                let words = [*v as u64, (*v >> 64) as u64];
                Ok(self
                    .ctx
                    .i128_type
                    .const_int_arbitrary_precision(&words)
                    .into())
            }
            Constant::Address(big) => {
                let bytes = big.to_bytes_le();
                let mut buf = [0u8; 32];
                let len = bytes.len().min(32);
                buf[..len].copy_from_slice(&bytes[..len]);
                let words: [u64; 4] = [
                    u64::from_le_bytes(buf[0..8].try_into().unwrap()),
                    u64::from_le_bytes(buf[8..16].try_into().unwrap()),
                    u64::from_le_bytes(buf[16..24].try_into().unwrap()),
                    u64::from_le_bytes(buf[24..32].try_into().unwrap()),
                ];
                Ok(self
                    .ctx
                    .i256_type
                    .const_int_arbitrary_precision(&words)
                    .into())
            }
            Constant::U256(v) => {
                let (hi, lo) = v.into_words();
                let words: [u64; 4] = [lo as u64, (lo >> 64) as u64, hi as u64, (hi >> 64) as u64];
                Ok(self
                    .ctx
                    .i256_type
                    .const_int_arbitrary_precision(&words)
                    .into())
            }
            Constant::ByteArray(bytes) => {
                let id = self.next_const_id();
                let global = self.emit_const_global(&format!("const_bytes_{id}"), bytes);
                let func = self.get_or_declare_runtime_fn(
                    "__move_rt_const_vec_u8",
                    self.ctx
                        .ptr_type
                        .fn_type(&[self.ctx.ptr_type.into(), self.ctx.i64_type.into()], false),
                );
                let ptr = global.as_pointer_value();
                let len = self.ctx.i64_type.const_int(bytes.len() as u64, false);
                let call = self
                    .ctx
                    .builder
                    .build_call(func, &[ptr.into(), len.into()], "const_vec_u8")
                    .unwrap();
                match call.try_as_basic_value() {
                    inkwell::values::ValueKind::Basic(v) => Ok(v),
                    _ => unreachable!("const vec runtime function must return a value"),
                }
            }
            Constant::AddressArray(addrs) => {
                let id = self.next_const_id();
                let buf = serialize_address_array(addrs);
                let global = self.emit_const_global(&format!("const_addrs_{id}"), &buf);
                let func = self.get_or_declare_runtime_fn(
                    "__move_rt_const_vec_address",
                    self.ctx
                        .ptr_type
                        .fn_type(&[self.ctx.ptr_type.into(), self.ctx.i64_type.into()], false),
                );
                let ptr = global.as_pointer_value();
                let count = self.ctx.i64_type.const_int(addrs.len() as u64, false);
                let call = self
                    .ctx
                    .builder
                    .build_call(func, &[ptr.into(), count.into()], "const_vec_addr")
                    .unwrap();
                match call.try_as_basic_value() {
                    inkwell::values::ValueKind::Basic(v) => Ok(v),
                    _ => unreachable!("const vec runtime function must return a value"),
                }
            }
            Constant::Vector(elems) => {
                let fn_type = self.ctx.ptr_type.fn_type(
                    &[
                        self.ctx.ptr_type.into(),
                        self.ctx.i64_type.into(),
                        self.ctx.i64_type.into(),
                    ],
                    false,
                );
                if elems.is_empty() {
                    let func = self.get_or_declare_runtime_fn("__move_rt_const_vec", fn_type);
                    let null = self.ctx.ptr_type.const_null();
                    let zero = self.ctx.i64_type.const_zero();
                    let call = self
                        .ctx
                        .builder
                        .build_call(
                            func,
                            &[null.into(), zero.into(), zero.into()],
                            "const_vec_empty",
                        )
                        .unwrap();
                    return match call.try_as_basic_value() {
                        inkwell::values::ValueKind::Basic(v) => Ok(v),
                        _ => unreachable!("const vec runtime function must return a value"),
                    };
                }
                let (elem_size, buf) = serialize_scalar_vector(elems)?;
                let id = self.next_const_id();
                let global = self.emit_const_global(&format!("const_vec_{id}"), &buf);
                let func = self.get_or_declare_runtime_fn("__move_rt_const_vec", fn_type);
                let ptr = global.as_pointer_value();
                let count = self.ctx.i64_type.const_int(elems.len() as u64, false);
                let esz = self.ctx.i64_type.const_int(elem_size as u64, false);
                let call = self
                    .ctx
                    .builder
                    .build_call(func, &[ptr.into(), count.into(), esz.into()], "const_vec")
                    .unwrap();
                match call.try_as_basic_value() {
                    inkwell::values::ValueKind::Basic(v) => Ok(v),
                    _ => unreachable!("const vec runtime function must return a value"),
                }
            }
        }
    }

    /// Allocate a unique ID for global constant names.
    fn next_const_id(&mut self) -> usize {
        let id = self.const_counter;
        self.const_counter += 1;
        id
    }

    /// Emit a private constant global containing the given bytes.
    fn emit_const_global(&self, name: &str, data: &[u8]) -> inkwell::values::GlobalValue<'ctx> {
        let arr_ty = self.ctx.i8_type.array_type(data.len() as u32);
        let arr_val = self.ctx.context.const_string(data, false);
        let global = self.ctx.module.add_global(arr_ty, None, name);
        global.set_initializer(&arr_val);
        global.set_constant(true);
        global.set_linkage(Linkage::Private);
        global.set_unnamed_addr(true);
        global
    }

    /// Get or declare an external runtime function.
    fn get_or_declare_runtime_fn(
        &self,
        symbol: &str,
        fn_type: inkwell::types::FunctionType<'ctx>,
    ) -> FunctionValue<'ctx> {
        match self.ctx.module.get_function(symbol) {
            Some(f) => f,
            None => self
                .ctx
                .module
                .add_function(symbol, fn_type, Some(Linkage::External)),
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
                let callee_env = self.env.get_module(*module_id).into_function(*fun_id);

                let (callee_fn, call_name) = if callee_env.is_native() {
                    // Native function: declare as extern with monomorphized symbol
                    let mangled = mangle_native_symbol(self.env, &callee_env, type_args);
                    let f = match self.ctx.module.get_function(&mangled) {
                        Some(f) => f,
                        None => {
                            let param_types: Vec<_> = callee_env
                                .get_parameter_types()
                                .iter()
                                .map(|t| t.instantiate(type_args))
                                .map(|t| {
                                    lower_model_type(self.ctx, self.env, &t).map(|lt| lt.into())
                                })
                                .collect::<Result<_, _>>()?;
                            let ret_types: Vec<Type> = callee_env
                                .get_return_types()
                                .iter()
                                .map(|t| t.instantiate(type_args))
                                .collect();
                            let fn_type =
                                build_fn_type(self.ctx, self.env, &ret_types, &param_types)?;
                            self.ctx
                                .module
                                .add_function(&mangled, fn_type, Some(Linkage::External))
                        }
                    };
                    (f, mangled)
                } else if !type_args.is_empty() {
                    // Monomorphize: compile a specialized copy of the callee
                    // with TypeParameters replaced by concrete types.
                    let inst_args = self.inst_types(type_args);
                    let callee_name = callee_env.get_name_str();
                    let mangled =
                        format!("{}${}", callee_name, mangle_type_args(self.env, &inst_args));
                    let f = match self.ctx.module.get_function(&mangled) {
                        Some(f) => f,
                        None => {
                            let param_types: Vec<_> = callee_env
                                .get_parameter_types()
                                .iter()
                                .map(|t| t.instantiate(&inst_args))
                                .map(|t| {
                                    lower_model_type(self.ctx, self.env, &t).map(|lt| lt.into())
                                })
                                .collect::<Result<_, _>>()?;
                            let ret_types: Vec<Type> = callee_env
                                .get_return_types()
                                .iter()
                                .map(|t| t.instantiate(&inst_args))
                                .collect();
                            let fn_type =
                                build_fn_type(self.ctx, self.env, &ret_types, &param_types)?;
                            let function = self.ctx.module.add_function(&mangled, fn_type, None);

                            let saved_block = self.ctx.builder.get_insert_block().unwrap();

                            let generator = StacklessBytecodeGenerator::new(&callee_env);
                            let func_data = generator.generate_function();
                            let param_count = callee_env.get_parameter_count();
                            let mut callee_lowering = FunctionLowering::new(
                                self.ctx,
                                self.env,
                                function,
                                param_count,
                                &func_data,
                                inst_args,
                            )?;
                            callee_lowering.lower_code(&func_data)?;

                            self.ctx.builder.position_at_end(saved_block);
                            function
                        }
                    };
                    (f, mangled)
                } else {
                    // Non-generic, non-native: look up in current LLVM module first
                    // (intra-module calls declared in pass 1), then fall back to an
                    // extern declaration for cross-module calls resolved at link time.
                    let callee_name = callee_env.get_name_str();
                    let f = match self.ctx.module.get_function(&callee_name) {
                        Some(f) => f,
                        None => {
                            let param_types: Vec<_> = callee_env
                                .get_parameter_types()
                                .iter()
                                .map(|t| {
                                    lower_model_type(self.ctx, self.env, t).map(|lt| lt.into())
                                })
                                .collect::<Result<_, _>>()?;
                            let ret_types = callee_env.get_return_types();
                            let fn_type =
                                build_fn_type(self.ctx, self.env, &ret_types, &param_types)?;
                            self.ctx.module.add_function(
                                &callee_name,
                                fn_type,
                                Some(Linkage::External),
                            )
                        }
                    };
                    (f, callee_name)
                };

                let args: Vec<_> = srcs
                    .iter()
                    .map(|s| self.load_value(*s).map(|v| v.into()))
                    .collect::<Result<_, _>>()?;

                let call = self
                    .ctx
                    .builder
                    .build_call(callee_fn, &args, &call_name)
                    .unwrap();

                if !dsts.is_empty() {
                    let ret_val = match call.try_as_basic_value() {
                        inkwell::values::ValueKind::Basic(v) => v,
                        _ => panic!("expected non-void return from callee"),
                    };
                    if dsts.len() == 1 {
                        self.store(dsts[0], ret_val);
                    } else {
                        // Multi-return: unpack struct into individual destinations
                        let struct_val = ret_val.into_struct_value();
                        for (i, dst) in dsts.iter().enumerate() {
                            let field = self
                                .ctx
                                .builder
                                .build_extract_value(struct_val, i as u32, &format!("call_ret_{i}"))
                                .unwrap();
                            self.store(*dst, field);
                        }
                    }
                }
                return Ok(());
            }

            // Pack: construct a struct from field values
            Operation::Pack(mid, did, type_args) => {
                let type_args = self.inst_types(type_args);
                let struct_ty =
                    lower_model_type(self.ctx, self.env, &Type::Datatype(*mid, *did, type_args))?
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
            Operation::Unpack(mid, did, _type_args) => {
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
                let struct_ptr = self.load_value(srcs[0])?.into_pointer_value();
                let type_args = self.inst_types(type_args);
                let struct_ty =
                    lower_model_type(self.ctx, self.env, &Type::Datatype(*mid, *did, type_args))?;
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
            Operation::GetField(_mid, _did, _type_args, offset) => {
                let struct_val = self.load_value(srcs[0])?.into_struct_value();
                let field_val = self
                    .ctx
                    .builder
                    .build_extract_value(struct_val, *offset as u32, "getfield")
                    .unwrap();
                self.store(dsts[0], field_val);
                return Ok(());
            }

            // Global storage operations: emit calls to __move_rt_* externs
            Operation::MoveTo(mid, did, type_args) => {
                return self.lower_storage_op(
                    "move_to",
                    *mid,
                    *did,
                    type_args,
                    dsts,
                    srcs,
                    |this, dt_ty, _| {
                        let val_ty = lower_model_type(this.ctx, this.env, &dt_ty)?.into();
                        Ok(this
                            .ctx
                            .context
                            .void_type()
                            .fn_type(&[val_ty, this.ctx.i256_type.into()], false))
                    },
                );
            }
            Operation::MoveFrom(mid, did, type_args) => {
                return self.lower_storage_op(
                    "move_from",
                    *mid,
                    *did,
                    type_args,
                    dsts,
                    srcs,
                    |this, dt_ty, _| {
                        let ret_ty = lower_model_type(this.ctx, this.env, &dt_ty)?;
                        Ok(ret_ty.fn_type(&[this.ctx.i256_type.into()], false))
                    },
                );
            }
            Operation::Exists(mid, did, type_args) => {
                return self.lower_storage_op(
                    "exists",
                    *mid,
                    *did,
                    type_args,
                    dsts,
                    srcs,
                    |this, _, _| {
                        Ok(this
                            .ctx
                            .i8_type
                            .fn_type(&[this.ctx.i256_type.into()], false))
                    },
                );
            }
            Operation::BorrowGlobal(mid, did, type_args) => {
                return self.lower_storage_op(
                    "borrow_global",
                    *mid,
                    *did,
                    type_args,
                    dsts,
                    srcs,
                    |this, _, _| {
                        Ok(this
                            .ctx
                            .ptr_type
                            .fn_type(&[this.ctx.i256_type.into()], false))
                    },
                );
            }
            Operation::GetGlobal(mid, did, type_args) => {
                return self.lower_storage_op(
                    "get_global",
                    *mid,
                    *did,
                    type_args,
                    dsts,
                    srcs,
                    |this, dt_ty, _| {
                        let ret_ty = lower_model_type(this.ctx, this.env, &dt_ty)?;
                        Ok(ret_ty.fn_type(&[this.ctx.i256_type.into()], false))
                    },
                );
            }

            // Destroy (Pop): no-op — LLVM manages alloca lifetimes
            Operation::Destroy => return Ok(()),

            other => {
                return Err(CompileError::UnsupportedOperation(format!("{:?}", other)));
            }
        };
        self.store(dsts[0], result.into());
        Ok(())
    }

    /// Emit a call to a `__move_rt_<op_name>$<mangled_type>` extern for a
    /// global storage operation (MoveTo, MoveFrom, Exists, BorrowGlobal, GetGlobal).
    #[allow(clippy::too_many_arguments)]
    fn lower_storage_op(
        &self,
        op_name: &str,
        mid: move_model::model::ModuleId,
        did: move_model::model::DatatypeId,
        type_args: &[Type],
        dsts: &[usize],
        srcs: &[usize],
        build_fn_type: impl FnOnce(
            &Self,
            Type,
            &str,
        ) -> Result<inkwell::types::FunctionType<'ctx>, CompileError>,
    ) -> Result<(), CompileError> {
        let inst_args = self.inst_types(type_args);
        let dt_ty = Type::Datatype(mid, did, inst_args);
        let mangled = mangle_type(self.env, &dt_ty);
        let symbol = format!("__move_rt_{op_name}${mangled}");

        let func = match self.ctx.module.get_function(&symbol) {
            Some(f) => f,
            None => {
                let fn_type = build_fn_type(self, dt_ty, &symbol)?;
                self.ctx
                    .module
                    .add_function(&symbol, fn_type, Some(Linkage::External))
            }
        };

        let args: Vec<_> = srcs
            .iter()
            .map(|s| self.load_value(*s).map(|v| v.into()))
            .collect::<Result<_, _>>()?;

        let call = self.ctx.builder.build_call(func, &args, &symbol).unwrap();

        if !dsts.is_empty() {
            let ret_val = match call.try_as_basic_value() {
                inkwell::values::ValueKind::Basic(v) => v,
                _ => panic!("expected non-void return from {symbol}"),
            };
            self.store(dsts[0], ret_val);
        }
        Ok(())
    }

    fn get_or_declare_abort_fn(&self) -> FunctionValue<'ctx> {
        match self.ctx.module.get_function("__move_rt_abort") {
            Some(f) => f,
            None => {
                let fn_type = self
                    .ctx
                    .context
                    .void_type()
                    .fn_type(&[self.ctx.i64_type.into()], false);
                self.ctx
                    .module
                    .add_function("__move_rt_abort", fn_type, Some(Linkage::External))
            }
        }
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

/// Serialize an `AddressArray` into a flat buffer of 32-byte little-endian addresses.
///
/// Uses little-endian to match the LLVM i256 representation used for
/// `Constant::Address` in `lower_constant`.
fn serialize_address_array(addrs: &[num_bigint::BigUint]) -> Vec<u8> {
    let mut buf = Vec::with_capacity(addrs.len() * 32);
    for addr in addrs {
        let bytes = addr.to_bytes_le();
        let mut padded = [0u8; 32];
        let len = bytes.len().min(32);
        padded[..len].copy_from_slice(&bytes[..len]);
        buf.extend_from_slice(&padded);
    }
    buf
}

/// Serialize a `Vector` of scalar constants into a flat byte buffer.
///
/// Returns `(element_size, serialized_bytes)`. Only handles scalar element types
/// (Bool, U8..U256, Address). Nested vectors are not supported.
fn serialize_scalar_vector(elems: &[Constant]) -> Result<(usize, Vec<u8>), CompileError> {
    let elem_size = match &elems[0] {
        Constant::Bool(_) | Constant::U8(_) => 1,
        Constant::U16(_) => 2,
        Constant::U32(_) => 4,
        Constant::U64(_) => 8,
        Constant::U128(_) => 16,
        Constant::U256(_) | Constant::Address(_) => 32,
        other => {
            return Err(CompileError::UnsupportedOperation(format!(
                "vector constant with non-scalar element: {:?}",
                other
            )));
        }
    };

    let mut buf = Vec::with_capacity(elems.len() * elem_size);
    for elem in elems {
        match elem {
            Constant::Bool(v) => buf.push(*v as u8),
            Constant::U8(v) => buf.push(*v),
            Constant::U16(v) => buf.extend_from_slice(&v.to_le_bytes()),
            Constant::U32(v) => buf.extend_from_slice(&v.to_le_bytes()),
            Constant::U64(v) => buf.extend_from_slice(&v.to_le_bytes()),
            Constant::U128(v) => buf.extend_from_slice(&v.to_le_bytes()),
            Constant::U256(v) => {
                let (hi, lo) = v.into_words();
                buf.extend_from_slice(&lo.to_le_bytes());
                buf.extend_from_slice(&hi.to_le_bytes());
            }
            Constant::Address(big) => {
                let bytes = big.to_bytes_le();
                let mut padded = [0u8; 32];
                let len = bytes.len().min(32);
                padded[..len].copy_from_slice(&bytes[..len]);
                buf.extend_from_slice(&padded);
            }
            other => {
                return Err(CompileError::UnsupportedOperation(format!(
                    "vector constant with non-scalar element: {:?}",
                    other
                )));
            }
        }
    }
    Ok((elem_size, buf))
}

/// Build an LLVM function type from Move return types and LLVM param types.
///
/// For zero returns → void, one return → that type, multiple returns → anonymous struct.
fn build_fn_type<'ctx>(
    ctx: &LlvmContext<'ctx>,
    env: &move_model::model::GlobalEnv,
    ret_types: &[Type],
    param_types: &[inkwell::types::BasicMetadataTypeEnum<'ctx>],
) -> Result<inkwell::types::FunctionType<'ctx>, CompileError> {
    Ok(if ret_types.is_empty() {
        ctx.context.void_type().fn_type(param_types, false)
    } else if ret_types.len() == 1 {
        let ret = lower_model_type(ctx, env, &ret_types[0])?;
        ret.fn_type(param_types, false)
    } else {
        let llvm_ret_types: Vec<BasicTypeEnum<'ctx>> = ret_types
            .iter()
            .map(|t| lower_model_type(ctx, env, t))
            .collect::<Result<_, _>>()?;
        let ret_struct = ctx.context.struct_type(&llvm_ret_types, false);
        ret_struct.fn_type(param_types, false)
    })
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
    let fn_type = build_fn_type(ctx, env, &func_data.return_types, &param_llvm_types)?;

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
    let mut lowering =
        FunctionLowering::new(ctx, env, function, param_count, func_data, Vec::new())?;
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
