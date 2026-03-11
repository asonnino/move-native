// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;
use std::collections::BTreeMap;

use inkwell::basic_block::BasicBlock;
use inkwell::module::Linkage;
use inkwell::types::BasicTypeEnum;
use inkwell::values::{
    BasicValueEnum, CallSiteValue, FunctionValue, IntValue, PointerValue, StructValue,
};
use move_model::model::FunctionEnv as MoveFunctionEnv;
use move_model::ty::Type;
use move_stackless_bytecode::function_target::FunctionData;
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Label};

use crate::context::LlvmContext;
use crate::error::{CompileError, CompileResult};
use crate::types::TypeLowering;

/// Extension trait for extracting a `BasicValueEnum` from a call result.
pub(crate) trait CallSiteValueExt<'ctx> {
    fn into_basic_value(self) -> CompileResult<BasicValueEnum<'ctx>>;
}

impl<'ctx> CallSiteValueExt<'ctx> for CallSiteValue<'ctx> {
    fn into_basic_value(self) -> CompileResult<BasicValueEnum<'ctx>> {
        let inkwell::values::ValueKind::Basic(v) = self.try_as_basic_value() else {
            return Err(CompileError::malformed_module(
                "expected non-void return from call",
            ));
        };
        Ok(v)
    }
}

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

impl<'ctx> Local<'ctx> {
    /// Create a new local: instantiate the Move type, lower it to LLVM, and emit an alloca.
    pub(crate) fn new(
        ctx: &LlvmContext<'ctx>,
        ty: &Type,
        type_params: &[Type],
        name: &str,
    ) -> CompileResult<Self> {
        let mty = if type_params.is_empty() {
            ty.clone()
        } else {
            ty.instantiate(type_params)
        };
        let llvm_ty = TypeLowering::new(ctx).lower_type(&mty)?;
        let alloca = ctx.builder.build_alloca(llvm_ty, name)?;
        Ok(Self {
            mty,
            llvm_ty,
            alloca,
        })
    }
}

/// Per-function infrastructure state and utility methods used by emitters.
///
/// Contains everything emitters need (locals, type params, mangling, LLVM helpers)
/// without exposing the orchestration surface (bytecode lowering, operation dispatch).
pub(crate) struct FunctionState<'a, 'ctx> {
    pub(crate) ctx: &'a LlvmContext<'ctx>,
    /// All locals (params + locals + compiler-generated temps).
    pub(crate) locals: Vec<Local<'ctx>>,
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
        function: FunctionValue<'ctx>,
        parameter_count: usize,
        function_data: &FunctionData,
        type_params: Vec<Type>,
    ) -> CompileResult<Self> {
        // Allocas for all locals
        let locals: Vec<Local> = function_data
            .local_types
            .iter()
            .enumerate()
            .map(|(i, ty)| Local::new(ctx, ty, &type_params, &format!("t{i}")))
            .collect::<CompileResult<_>>()?;

        // Store function parameters into their allocas
        for (i, local) in locals.iter().enumerate().take(parameter_count) {
            let parameter = function
                .get_nth_param(i as u32)
                .ok_or(CompileError::llvm("missing parameter"))?;
            ctx.builder.build_store(local.alloca, parameter)?;
        }

        // Pre-create basic blocks for all labels
        let mut label_blocks = BTreeMap::new();
        for byte_code in &function_data.code {
            if let Bytecode::Label(_, label) = byte_code {
                let block = ctx
                    .context
                    .append_basic_block(function, &format!("L{}", label.as_usize()));
                label_blocks.insert(*label, block);
            }
        }

        Ok(Self {
            ctx,
            locals,
            label_blocks,
            type_params,
            const_counter: Cell::new(0),
        })
    }

    /// Instantiate type_args through the current function's type parameters.
    /// Returns the args unchanged for non-generic functions.
    pub(crate) fn instantiate_types(&self, types: &[Type]) -> Vec<Type> {
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

    /// Get a local by index, returning an error if out of bounds.
    pub(crate) fn get_local(&self, idx: usize) -> CompileResult<&Local<'ctx>> {
        self.locals.get(idx).ok_or_else(|| {
            CompileError::malformed_module(format!("local index {idx} out of bounds"))
        })
    }

    /// Get a label's basic block, returning an error if the label doesn't exist.
    pub(crate) fn get_label_block(
        &self,
        label: &move_stackless_bytecode::stackless_bytecode::Label,
    ) -> CompileResult<BasicBlock<'ctx>> {
        self.label_blocks.get(label).copied().ok_or_else(|| {
            CompileError::malformed_module(format!("unknown label {}", label.as_usize()))
        })
    }

    /// Load a local as a generic `BasicValueEnum` (works for any type).
    pub(crate) fn load_value(&self, idx: usize) -> CompileResult<BasicValueEnum<'ctx>> {
        let local = self.get_local(idx)?;
        Ok(self
            .ctx
            .builder
            .build_load(local.llvm_ty, local.alloca, &format!("t{idx}"))?)
    }

    /// Load a local as an `IntValue` (convenience for arithmetic/comparison ops).
    pub(crate) fn load_int(&self, idx: usize) -> CompileResult<IntValue<'ctx>> {
        match self.load_value(idx)? {
            BasicValueEnum::IntValue(v) => Ok(v),
            other => Err(CompileError::malformed_module(format!(
                "expected integer for local {idx}, got {other:?}"
            ))),
        }
    }

    /// Load a local as a `StructValue` (convenience for struct pack/unpack ops).
    pub(crate) fn load_struct(&self, idx: usize) -> CompileResult<StructValue<'ctx>> {
        match self.load_value(idx)? {
            BasicValueEnum::StructValue(v) => Ok(v),
            other => Err(CompileError::malformed_module(format!(
                "expected struct for local {idx}, got {other:?}"
            ))),
        }
    }

    /// Load a local as a `PointerValue` (convenience for reference ops).
    pub(crate) fn load_pointer(&self, idx: usize) -> CompileResult<PointerValue<'ctx>> {
        match self.load_value(idx)? {
            BasicValueEnum::PointerValue(v) => Ok(v),
            other => Err(CompileError::malformed_module(format!(
                "expected pointer for local {idx}, got {other:?}"
            ))),
        }
    }

    /// Store a value into a local's alloca.
    pub(crate) fn store(&self, idx: usize, val: BasicValueEnum<'ctx>) -> CompileResult<()> {
        let local = self.get_local(idx)?;
        self.ctx.builder.build_store(local.alloca, val)?;
        Ok(())
    }

    /// Resolve the pointee LLVM type for a local that holds a reference (`&T` or `&mut T`).
    pub(crate) fn pointee_type(&self, idx: usize) -> CompileResult<BasicTypeEnum<'ctx>> {
        let local = self.get_local(idx)?;
        match &local.mty {
            Type::Reference(_, inner) => self.lower_type(inner),
            other => Err(CompileError::unsupported_type(other.clone())),
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
