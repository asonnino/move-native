// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

mod calls;
mod constants;
mod storage;

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;

use inkwell::IntPredicate;
use inkwell::basic_block::BasicBlock;
use inkwell::module::Linkage;
use inkwell::types::{BasicTypeEnum, IntType};
use inkwell::values::{BasicValueEnum, FunctionValue, IntValue, PointerValue};
use move_model::ty::Type;
use move_stackless_bytecode::function_target::FunctionData;
use move_stackless_bytecode::stackless_bytecode::{AssignKind, Bytecode, Label, Operation};

use crate::compiler::Compiler;
use crate::error::{CompileError, CompileResult};

use calls::CallEmitter;
use constants::ConstantEmitter;
use storage::StorageEmitter;

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
pub(crate) struct FunctionLowering<'a, 'ctx> {
    pub(crate) compiler: &'a Compiler<'ctx>,
    /// All locals (params + locals + compiler-generated temps).
    locals: RefCell<Vec<Local<'ctx>>>,
    /// Pre-created basic blocks for each Label in the bytecode.
    label_blocks: BTreeMap<Label, BasicBlock<'ctx>>,
    /// Concrete types for the function's type parameters (empty for non-generic).
    type_params: Vec<Type>,
    /// Counter for unique global constant names.
    const_counter: Cell<usize>,
}

impl<'a, 'ctx> FunctionLowering<'a, 'ctx> {
    pub fn new(
        compiler: &'a Compiler<'ctx>,
        function: FunctionValue<'ctx>,
        param_count: usize,
        func_data: &FunctionData,
        type_params: Vec<Type>,
    ) -> CompileResult<Self> {
        let ctx = &compiler.ctx;
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
            let llvm_ty = compiler.lower_type(&mty)?;
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
            compiler,
            locals: RefCell::new(locals),
            label_blocks,
            type_params,
            const_counter: Cell::new(0),
        })
    }

    /// Instantiate type_args through the current function's type parameters.
    /// Returns the args unchanged for non-generic functions.
    pub(crate) fn inst_types(&self, types: &[Type]) -> Vec<Type> {
        if self.type_params.is_empty() {
            types.to_vec()
        } else {
            types
                .iter()
                .map(|t| t.instantiate(&self.type_params))
                .collect()
        }
    }

    pub fn lower_code(&self, func_data: &FunctionData) -> CompileResult<()> {
        for bc in &func_data.code {
            self.lower_bytecode(bc)?;
        }
        Ok(())
    }

    fn lower_bytecode(&self, bc: &Bytecode) -> CompileResult<()> {
        let ctx = &self.compiler.ctx;
        match bc {
            Bytecode::Assign(_, dst, src, kind) => {
                // Move-swap optimization: for Move of struct types, swap the
                // local slots instead of load+store. Move guarantees the source
                // is dead after this point, so reusing its alloca is safe and
                // avoids an unnecessary copy.
                if matches!(kind, AssignKind::Move) && self.locals.borrow()[*src].mty.is_struct() {
                    let cloned = self.locals.borrow()[*src].clone();
                    self.locals.borrow_mut()[*dst] = cloned;
                } else {
                    let val = self.load_value(*src)?;
                    self.store(*dst, val);
                }
            }
            Bytecode::Load(_, dst, constant) => {
                let val = ConstantEmitter::new(self).lower(constant)?;
                self.store(*dst, val);
            }
            Bytecode::Call(_, dsts, op, srcs, _) => {
                self.lower_operation(dsts, op, srcs)?;
            }
            Bytecode::Ret(_, rets) => {
                if rets.is_empty() {
                    ctx.builder.build_return(None).unwrap();
                } else if rets.len() == 1 {
                    let val = self.load_value(rets[0])?;
                    ctx.builder.build_return(Some(&val)).unwrap();
                } else {
                    // Multi-return: pack values into an anonymous struct
                    let locals = self.locals.borrow();
                    let ret_types: Vec<BasicTypeEnum<'ctx>> = rets
                        .iter()
                        .map(|r| Ok(locals[*r].llvm_ty))
                        .collect::<CompileResult<_>>()?;
                    let ret_struct_ty = ctx.context.struct_type(&ret_types, false);
                    let mut agg = ret_struct_ty.get_undef();
                    for (i, r) in rets.iter().enumerate() {
                        let val = self.load_value(*r)?;
                        agg = ctx
                            .builder
                            .build_insert_value(agg, val, i as u32, &format!("ret_{i}"))
                            .unwrap()
                            .into_struct_value();
                    }
                    ctx.builder.build_return(Some(&agg)).unwrap();
                }
            }
            Bytecode::Label(_, label) => {
                let block = self.label_blocks[label];
                // Add fallthrough branch if current block has no terminator
                let current = ctx.builder.get_insert_block().unwrap();
                if current.get_terminator().is_none() {
                    ctx.builder.build_unconditional_branch(block).unwrap();
                }
                ctx.builder.position_at_end(block);
            }
            Bytecode::Jump(_, label) => {
                let block = self.label_blocks[label];
                ctx.builder.build_unconditional_branch(block).unwrap();
            }
            Bytecode::Branch(_, then_label, else_label, cond) => {
                let cond_val = self.load_int(*cond)?;
                let zero = cond_val.get_type().const_zero();
                let cmp = ctx
                    .builder
                    .build_int_compare(IntPredicate::NE, cond_val, zero, "cond")
                    .unwrap();
                let then_block = self.label_blocks[then_label];
                let else_block = self.label_blocks[else_label];
                ctx.builder
                    .build_conditional_branch(cmp, then_block, else_block)
                    .unwrap();
            }
            Bytecode::Abort(_, code_idx) => {
                let code = self.load_value(*code_idx)?;
                let abort_fn = self.compiler.get_or_declare_extern(
                    "__move_rt_abort",
                    ctx.context
                        .void_type()
                        .fn_type(&[ctx.i64_type.into()], false),
                );
                ctx.builder
                    .build_call(abort_fn, &[code.into()], "abort")
                    .unwrap();
                ctx.builder.build_unreachable().unwrap();
            }
            Bytecode::Nop(_) => {}
            other => {
                return Err(CompileError::UnsupportedBytecode(format!("{:?}", other)));
            }
        }
        Ok(())
    }

    /// Load a local as a generic `BasicValueEnum` (works for any type).
    pub(crate) fn load_value(&self, idx: usize) -> CompileResult<BasicValueEnum<'ctx>> {
        let locals = self.locals.borrow();
        let local = &locals[idx];
        Ok(self
            .compiler
            .ctx
            .builder
            .build_load(local.llvm_ty, local.alloca, &format!("t{idx}"))
            .unwrap())
    }

    /// Load a local as an `IntValue` (convenience for arithmetic/comparison ops).
    pub(crate) fn load_int(&self, idx: usize) -> CompileResult<IntValue<'ctx>> {
        Ok(self.load_value(idx)?.into_int_value())
    }

    /// Store a value into a local's alloca.
    pub(crate) fn store(&self, idx: usize, val: BasicValueEnum<'ctx>) {
        let locals = self.locals.borrow();
        self.compiler
            .ctx
            .builder
            .build_store(locals[idx].alloca, val)
            .unwrap();
    }

    /// Resolve the pointee LLVM type for a local that holds a reference (`&T` or `&mut T`).
    pub(crate) fn pointee_type(&self, idx: usize) -> CompileResult<BasicTypeEnum<'ctx>> {
        let locals = self.locals.borrow();
        match &locals[idx].mty {
            Type::Reference(_, inner) => self.compiler.lower_type(inner),
            other => Err(CompileError::UnsupportedType(format!(
                "expected reference type, got {:?}",
                other
            ))),
        }
    }

    /// Allocate a unique ID for global constant names.
    pub(crate) fn next_const_id(&self) -> usize {
        let id = self.const_counter.get();
        self.const_counter.set(id + 1);
        id
    }

    /// Emit a private constant global containing the given bytes.
    pub(crate) fn emit_const_global(
        &self,
        name: &str,
        data: &[u8],
    ) -> inkwell::values::GlobalValue<'ctx> {
        let ctx = &self.compiler.ctx;
        let arr_ty = ctx.i8_type.array_type(data.len() as u32);
        let arr_val = ctx.context.const_string(data, false);
        let global = ctx.module.add_global(arr_ty, None, name);
        global.set_initializer(&arr_val);
        global.set_constant(true);
        global.set_linkage(Linkage::Private);
        global.set_unnamed_addr(true);
        global
    }

    fn lower_operation(&self, dsts: &[usize], op: &Operation, srcs: &[usize]) -> CompileResult<()> {
        let ctx = &self.compiler.ctx;
        let result = match op {
            // Arithmetic: two same-type integers -> same type
            Operation::Add | Operation::Sub | Operation::Mul | Operation::Div | Operation::Mod => {
                let lhs = self.load_int(srcs[0])?;
                let rhs = self.load_int(srcs[1])?;
                match op {
                    Operation::Add => ctx.builder.build_int_add(lhs, rhs, "add").unwrap(),
                    Operation::Sub => ctx.builder.build_int_sub(lhs, rhs, "sub").unwrap(),
                    Operation::Mul => ctx.builder.build_int_mul(lhs, rhs, "mul").unwrap(),
                    Operation::Div => ctx.builder.build_int_unsigned_div(lhs, rhs, "div").unwrap(),
                    Operation::Mod => ctx.builder.build_int_unsigned_rem(lhs, rhs, "mod").unwrap(),
                    _ => unreachable!(),
                }
            }

            // Comparisons: two same-type integers -> bool (i8)
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
                let cmp = ctx
                    .builder
                    .build_int_compare(pred, lhs, rhs, "cmp")
                    .unwrap();
                ctx.builder
                    .build_int_z_extend(cmp, ctx.i8_type, "cmp_ext")
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
                let cmp = ctx
                    .builder
                    .build_int_compare(pred, lhs, rhs, "cmp")
                    .unwrap();
                ctx.builder
                    .build_int_z_extend(cmp, ctx.i8_type, "cmp_ext")
                    .unwrap()
            }

            // Bitwise: two same-type integers -> same type
            Operation::BitAnd => {
                let lhs = self.load_int(srcs[0])?;
                let rhs = self.load_int(srcs[1])?;
                ctx.builder.build_and(lhs, rhs, "and").unwrap()
            }
            Operation::BitOr => {
                let lhs = self.load_int(srcs[0])?;
                let rhs = self.load_int(srcs[1])?;
                ctx.builder.build_or(lhs, rhs, "or").unwrap()
            }
            Operation::Xor => {
                let lhs = self.load_int(srcs[0])?;
                let rhs = self.load_int(srcs[1])?;
                ctx.builder.build_xor(lhs, rhs, "xor").unwrap()
            }

            // Shifts: value (any width) + shift amount (u8) -> same type as value
            Operation::Shl | Operation::Shr => {
                let val = self.load_int(srcs[0])?;
                let amt = self.load_int(srcs[1])?;
                let amt = if amt.get_type().get_bit_width() < val.get_type().get_bit_width() {
                    ctx.builder
                        .build_int_z_extend(amt, val.get_type(), "shl_ext")
                        .unwrap()
                } else {
                    amt
                };
                if matches!(op, Operation::Shl) {
                    ctx.builder.build_left_shift(val, amt, "shl").unwrap()
                } else {
                    ctx.builder
                        .build_right_shift(val, amt, false, "shr")
                        .unwrap()
                }
            }

            // Logical AND/OR: two bools (i8) -> bool (i8)
            Operation::And => {
                let lhs = self.load_int(srcs[0])?;
                let rhs = self.load_int(srcs[1])?;
                ctx.builder.build_and(lhs, rhs, "land").unwrap()
            }
            Operation::Or => {
                let lhs = self.load_int(srcs[0])?;
                let rhs = self.load_int(srcs[1])?;
                ctx.builder.build_or(lhs, rhs, "lor").unwrap()
            }

            // Logical NOT: bool (i8) -> bool (i8), implemented as XOR with 1
            Operation::Not => {
                let src = self.load_int(srcs[0])?;
                let one = ctx.i8_type.const_int(1, false);
                ctx.builder.build_xor(src, one, "not").unwrap()
            }

            // Integer casts
            Operation::CastU8 => self.lower_cast(srcs[0], ctx.i8_type)?,
            Operation::CastU16 => self.lower_cast(srcs[0], ctx.i16_type)?,
            Operation::CastU32 => self.lower_cast(srcs[0], ctx.i32_type)?,
            Operation::CastU64 => self.lower_cast(srcs[0], ctx.i64_type)?,
            Operation::CastU128 => self.lower_cast(srcs[0], ctx.i128_type)?,
            Operation::CastU256 => self.lower_cast(srcs[0], ctx.i256_type)?,

            // Function call: delegate to CallEmitter
            Operation::Function(module_id, fun_id, type_args) => {
                return CallEmitter::new(self).emit(dsts, *module_id, *fun_id, type_args, srcs);
            }

            // Pack: construct a struct from field values
            Operation::Pack(mid, did, type_args) => {
                let type_args = self.inst_types(type_args);
                let struct_ty = self
                    .compiler
                    .lower_type(&Type::Datatype(*mid, *did, type_args))?
                    .into_struct_type();
                let mut agg = struct_ty.get_undef();
                for (i, src) in srcs.iter().enumerate() {
                    let field_val = self.load_value(*src)?;
                    agg = ctx
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
                let struct_env = self
                    .compiler
                    .mangler
                    .env()
                    .get_module(*mid)
                    .into_struct(*did);
                let field_count = struct_env.get_fields().count();
                for (i, dst) in dsts.iter().enumerate().take(field_count) {
                    let field_val = ctx
                        .builder
                        .build_extract_value(struct_val, i as u32, &format!("unpack_{i}"))
                        .unwrap();
                    self.store(*dst, field_val);
                }
                return Ok(());
            }

            // BorrowLoc: take the address of a local -> &T
            Operation::BorrowLoc => {
                let ptr = self.locals.borrow()[srcs[0]].alloca;
                self.store(dsts[0], ptr.into());
                return Ok(());
            }

            // BorrowField: GEP into a struct through a reference -> &Field
            Operation::BorrowField(mid, did, type_args, offset) => {
                let struct_ptr = self.load_value(srcs[0])?.into_pointer_value();
                let type_args = self.inst_types(type_args);
                let struct_ty = self
                    .compiler
                    .lower_type(&Type::Datatype(*mid, *did, type_args))?;
                let field_ptr = ctx
                    .builder
                    .build_struct_gep(struct_ty, struct_ptr, *offset as u32, "borrow_field")
                    .unwrap();
                self.store(dsts[0], field_ptr.into());
                return Ok(());
            }

            // ReadRef: load through a reference -> T
            Operation::ReadRef => {
                let ptr = self.load_value(srcs[0])?.into_pointer_value();
                let pointee_ty = self.pointee_type(srcs[0])?;
                let val = ctx.builder.build_load(pointee_ty, ptr, "read_ref").unwrap();
                self.store(dsts[0], val);
                return Ok(());
            }

            // WriteRef: store through a mutable reference
            Operation::WriteRef => {
                let ptr = self.load_value(srcs[0])?.into_pointer_value();
                let val = self.load_value(srcs[1])?;
                ctx.builder.build_store(ptr, val).unwrap();
                return Ok(());
            }

            // FreezeRef: &mut T -> &T (no-op, just copy the pointer)
            Operation::FreezeRef => {
                let ptr = self.load_value(srcs[0])?;
                self.store(dsts[0], ptr);
                return Ok(());
            }

            // GetField: extract a single field from a struct
            Operation::GetField(_mid, _did, _type_args, offset) => {
                let struct_val = self.load_value(srcs[0])?.into_struct_value();
                let field_val = ctx
                    .builder
                    .build_extract_value(struct_val, *offset as u32, "getfield")
                    .unwrap();
                self.store(dsts[0], field_val);
                return Ok(());
            }

            // Global storage operations: delegate to StorageEmitter
            Operation::MoveTo(mid, did, type_args) => {
                return StorageEmitter::new(self).emit_move_to(*mid, *did, type_args, dsts, srcs);
            }
            Operation::MoveFrom(mid, did, type_args) => {
                return StorageEmitter::new(self).emit_move_from(*mid, *did, type_args, dsts, srcs);
            }
            Operation::Exists(mid, did, type_args) => {
                return StorageEmitter::new(self).emit_exists(*mid, *did, type_args, dsts, srcs);
            }
            Operation::BorrowGlobal(mid, did, type_args) => {
                return StorageEmitter::new(self)
                    .emit_borrow_global(*mid, *did, type_args, dsts, srcs);
            }
            Operation::GetGlobal(mid, did, type_args) => {
                return StorageEmitter::new(self)
                    .emit_get_global(*mid, *did, type_args, dsts, srcs);
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

    fn lower_cast(&self, src: usize, target_ty: IntType<'ctx>) -> CompileResult<IntValue<'ctx>> {
        let ctx = &self.compiler.ctx;
        let val = self.load_int(src)?;
        let src_bits = val.get_type().get_bit_width();
        let dst_bits = target_ty.get_bit_width();
        Ok(if src_bits > dst_bits {
            ctx.builder
                .build_int_truncate(val, target_ty, "cast")
                .unwrap()
        } else if src_bits < dst_bits {
            ctx.builder
                .build_int_z_extend(val, target_ty, "cast")
                .unwrap()
        } else {
            val
        })
    }
}
