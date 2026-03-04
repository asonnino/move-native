// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;

use inkwell::basic_block::BasicBlock;
use inkwell::module::Linkage;
use inkwell::types::BasicTypeEnum;
use inkwell::values::{BasicValueEnum, FunctionValue, IntValue, PointerValue};
use move_model::model::FunctionEnv as MoveFunctionEnv;
use move_model::ty::Type;
use move_stackless_bytecode::stackless_bytecode::Label;

use crate::context::LlvmContext;
use crate::error::{CompileError, CompileResult};
use crate::types::TypeLowering;

/// A single local variable (param, local, or compiler-generated temp).
///
/// Bundles the Move type, LLVM type, and alloca pointer together so they
/// cannot get out of sync.
#[derive(Clone)]
pub(crate) struct Local<'ctx> {
    /// The Move-level type of this local.
    pub(crate) mty: Type,
    /// The lowered LLVM type (cached to avoid re-lowering on every load).
    pub(crate) llvm_ty: BasicTypeEnum<'ctx>,
    /// The alloca in the entry block that backs this local.
    pub(crate) alloca: PointerValue<'ctx>,
}

/// Per-function infrastructure state and utility methods used by emitters.
///
/// Contains everything emitters need (locals, type params, mangling, LLVM helpers)
/// without exposing the orchestration surface (bytecode lowering, operation dispatch).
pub(crate) struct FunctionState<'a, 'ctx> {
    pub(crate) ctx: &'a LlvmContext<'ctx>,
    /// All locals (params + locals + compiler-generated temps).
    pub(crate) locals: RefCell<Vec<Local<'ctx>>>,
    /// Pre-created basic blocks for each Label in the bytecode.
    pub(crate) label_blocks: BTreeMap<Label, BasicBlock<'ctx>>,
    /// Concrete types for the function's type parameters (empty for non-generic).
    type_params: Vec<Type>,
    /// Counter for unique global constant names.
    const_counter: Cell<usize>,
}

impl<'a, 'ctx> FunctionState<'a, 'ctx> {
    pub(crate) fn new(
        ctx: &'a LlvmContext<'ctx>,
        locals: Vec<Local<'ctx>>,
        label_blocks: BTreeMap<Label, BasicBlock<'ctx>>,
        type_params: Vec<Type>,
    ) -> Self {
        Self {
            ctx,
            locals: RefCell::new(locals),
            label_blocks,
            type_params,
            const_counter: Cell::new(0),
        }
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

    /// Lower a Move type to an LLVM type.
    pub(crate) fn lower_type(&self, ty: &Type) -> CompileResult<BasicTypeEnum<'ctx>> {
        TypeLowering::new(self.ctx).lower_type(ty)
    }

    /// Lower Move parameter and return types into an LLVM function type.
    pub(crate) fn lower_function_type(
        &self,
        parameter_types: &[Type],
        return_types: &[Type],
    ) -> CompileResult<inkwell::types::FunctionType<'ctx>> {
        TypeLowering::new(self.ctx).lower_function_type(parameter_types, return_types)
    }

    /// Declare an external runtime function (e.g. `__move_rt_*`).
    pub(crate) fn declare_external(
        &self,
        name: &str,
        fn_type: inkwell::types::FunctionType<'ctx>,
    ) -> FunctionValue<'ctx> {
        self.ctx.add_external_function(name, fn_type)
    }

    /// Mangle a Move type.
    pub(crate) fn mangle_type(&self, ty: &Type) -> CompileResult<String> {
        self.ctx.mangle_type(ty)
    }

    /// Mangle type arguments.
    pub(crate) fn mangle_type_args(&self, type_args: &[Type]) -> CompileResult<String> {
        self.ctx.mangle_type_args(type_args)
    }

    /// Mangle a native symbol.
    pub(crate) fn mangle_native_symbol(
        &self,
        callee_env: &MoveFunctionEnv<'_>,
        type_args: &[Type],
    ) -> CompileResult<String> {
        self.ctx.mangle_native_symbol(callee_env, type_args)
    }

    /// Load a local as a generic `BasicValueEnum` (works for any type).
    pub(crate) fn load_value(&self, idx: usize) -> CompileResult<BasicValueEnum<'ctx>> {
        let locals = self.locals.borrow();
        let local = &locals[idx];
        Ok(self
            .ctx
            .builder
            .build_load(local.llvm_ty, local.alloca, &format!("t{idx}"))?)
    }

    /// Load a local as an `IntValue` (convenience for arithmetic/comparison ops).
    pub(crate) fn load_int(&self, idx: usize) -> CompileResult<IntValue<'ctx>> {
        Ok(self.load_value(idx)?.into_int_value())
    }

    /// Store a value into a local's alloca.
    pub(crate) fn store(&self, idx: usize, val: BasicValueEnum<'ctx>) -> CompileResult<()> {
        let locals = self.locals.borrow();
        self.ctx.builder.build_store(locals[idx].alloca, val)?;
        Ok(())
    }

    /// Resolve the pointee LLVM type for a local that holds a reference (`&T` or `&mut T`).
    pub(crate) fn pointee_type(&self, idx: usize) -> CompileResult<BasicTypeEnum<'ctx>> {
        let locals = self.locals.borrow();
        match &locals[idx].mty {
            Type::Reference(_, inner) => self.lower_type(inner),
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
        let ctx = &self.ctx;
        let arr_ty = ctx.i8_type.array_type(data.len() as u32);
        let arr_val = ctx.context.const_string(data, false);
        let global = ctx.module.add_global(arr_ty, None, name);
        global.set_initializer(&arr_val);
        global.set_constant(true);
        global.set_linkage(Linkage::Private);
        global.set_unnamed_addr(true);
        global
    }
}
