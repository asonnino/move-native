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
use move_model::ty::{PrimitiveType, Type};
use move_stackless_bytecode::function_target::FunctionData;
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Label};

use crate::context::LlvmContext;
use crate::error::{CompileError, CompileResult, to_field_index};
use crate::types::TypeLowering;

/// Extension trait for extracting a `BasicValueEnum` from a call result.
pub(crate) trait CallSiteValueExt<'ctx> {
    fn into_basic_value(self) -> CompileResult<BasicValueEnum<'ctx>>;
}

impl<'ctx> CallSiteValueExt<'ctx> for CallSiteValue<'ctx> {
    fn into_basic_value(self) -> CompileResult<BasicValueEnum<'ctx>> {
        let inkwell::values::ValueKind::Basic(v) = self.try_as_basic_value() else {
            return Err(CompileError::TypeMismatch(
                "expected non-void return from call".into(),
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
            // Erase surviving type parameters (phantom) to a dummy concrete type.
            FunctionState::erase_type_params(ty.clone())
        } else {
            FunctionState::erase_type_params(ty.instantiate(type_params))
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
        let locals: Vec<Local> = function_data
            .local_types
            .iter()
            .enumerate()
            .map(|(i, ty)| Local::new(ctx, ty, &type_params, &format!("t{i}")))
            .collect::<CompileResult<_>>()?;

        for (i, local) in locals.iter().enumerate().take(parameter_count) {
            let parameter = function
                .get_nth_param(to_field_index(i)?)
                .expect("LLVM parameter count mismatch");
            ctx.builder.build_store(local.alloca, parameter)?;
        }

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

    pub(crate) fn get_local(&self, idx: usize) -> CompileResult<&Local<'ctx>> {
        self.locals.get(idx).ok_or_else(|| {
            CompileError::InvalidReference(format!("local index {idx} out of bounds"))
        })
    }

    pub(crate) fn get_label_block(
        &self,
        label: &move_stackless_bytecode::stackless_bytecode::Label,
    ) -> CompileResult<BasicBlock<'ctx>> {
        self.label_blocks.get(label).copied().ok_or_else(|| {
            CompileError::InvalidReference(format!("unknown label {}", label.as_usize()))
        })
    }

    pub(crate) fn load_value(&self, idx: usize) -> CompileResult<BasicValueEnum<'ctx>> {
        let local = self.get_local(idx)?;
        Ok(self
            .ctx
            .builder
            .build_load(local.llvm_ty, local.alloca, &format!("t{idx}"))?)
    }

    pub(crate) fn load_int(&self, idx: usize) -> CompileResult<IntValue<'ctx>> {
        match self.load_value(idx)? {
            BasicValueEnum::IntValue(v) => Ok(v),
            other => Err(CompileError::TypeMismatch(format!(
                "expected integer for local t{idx} (move type {:?}), got LLVM {}",
                self.get_local(idx)?.mty,
                Self::llvm_type_name(&other),
            ))),
        }
    }

    pub(crate) fn load_struct(&self, idx: usize) -> CompileResult<StructValue<'ctx>> {
        match self.load_value(idx)? {
            BasicValueEnum::StructValue(v) => Ok(v),
            other => Err(CompileError::TypeMismatch(format!(
                "expected struct for local t{idx} (move type {:?}), got LLVM {}",
                self.get_local(idx)?.mty,
                Self::llvm_type_name(&other),
            ))),
        }
    }

    pub(crate) fn load_pointer(&self, idx: usize) -> CompileResult<PointerValue<'ctx>> {
        match self.load_value(idx)? {
            BasicValueEnum::PointerValue(v) => Ok(v),
            other => Err(CompileError::TypeMismatch(format!(
                "expected pointer for local t{idx} (move type {:?}), got LLVM {}",
                self.get_local(idx)?.mty,
                Self::llvm_type_name(&other),
            ))),
        }
    }

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
            other => Err(CompileError::TypeMismatch(format!(
                "expected reference type for pointee_type, got {other:?}"
            ))),
        }
    }

    /// Instantiate type_args through the current function's type parameters.
    /// Returns the args unchanged for non-generic functions.
    ///
    /// Any `TypeParameter` values that survive instantiation are erased to a
    /// dummy concrete type (`U64`). This happens for phantom type parameters
    /// when a phantom-generic function is compiled at top level with empty
    /// `type_params` — the Move verifier guarantees the surviving parameters
    /// are phantom, so the concrete type chosen does not affect layout.
    pub(crate) fn instantiate_types(&self, types: &[Type]) -> Vec<Type> {
        let instantiated = if self.type_params.is_empty() {
            types.to_vec()
        } else {
            types
                .iter()
                .map(|t| t.instantiate(&self.type_params))
                .collect()
        };
        instantiated
            .into_iter()
            .map(Self::erase_type_params)
            .collect()
    }

    pub(crate) fn lower_type(&self, ty: &Type) -> CompileResult<BasicTypeEnum<'ctx>> {
        TypeLowering::new(self.ctx).lower_type(ty)
    }

    pub(crate) fn lower_function_type(
        &self,
        parameter_types: &[Type],
        return_types: &[Type],
    ) -> CompileResult<inkwell::types::FunctionType<'ctx>> {
        TypeLowering::new(self.ctx).lower_function_type(parameter_types, return_types)
    }

    pub(crate) fn declare_external(
        &self,
        name: &str,
        fn_type: inkwell::types::FunctionType<'ctx>,
    ) -> FunctionValue<'ctx> {
        self.ctx.add_external_function(name, fn_type)
    }

    pub(crate) fn mangle_type(&self, ty: &Type) -> CompileResult<String> {
        self.ctx.mangle_type(ty)
    }

    pub(crate) fn mangle_type_args(&self, type_args: &[Type]) -> CompileResult<String> {
        self.ctx.mangle_type_args(type_args)
    }

    pub(crate) fn mangle_native_symbol(
        &self,
        callee_env: &MoveFunctionEnv<'_>,
        type_args: &[Type],
    ) -> CompileResult<String> {
        self.ctx.mangle_native_symbol(callee_env, type_args)
    }

    pub(crate) fn next_const_id(&self) -> usize {
        let id = self.const_counter.get();
        self.const_counter.set(id + 1);
        id
    }

    pub(crate) fn emit_const_global(
        &self,
        name: &str,
        data: &[u8],
    ) -> CompileResult<inkwell::values::GlobalValue<'ctx>> {
        let ctx = &self.ctx;
        let len = u32::try_from(data.len()).map_err(|_| {
            CompileError::internal(format!("constant data length {} exceeds u32", data.len()))
        })?;
        let arr_ty = ctx.i8_type.array_type(len);
        let arr_val = ctx.context.const_string(data, false);
        let global = ctx.module.add_global(arr_ty, None, name);
        global.set_initializer(&arr_val);
        global.set_constant(true);
        global.set_linkage(Linkage::Private);
        global.set_unnamed_addr(true);
        Ok(global)
    }

    /// Replace any remaining `TypeParameter` with a dummy concrete type (`U64`).
    ///
    /// Surviving type parameters must be phantom (the compiler only compiles
    /// functions at top level when all type params are phantom), so the
    /// concrete type chosen does not affect layout or codegen.
    pub(super) fn erase_type_params(ty: Type) -> Type {
        match ty {
            Type::TypeParameter(_) => Type::Primitive(PrimitiveType::U64),
            Type::Vector(inner) => Type::Vector(Box::new(Self::erase_type_params(*inner))),
            Type::Reference(m, inner) => {
                Type::Reference(m, Box::new(Self::erase_type_params(*inner)))
            }
            Type::Datatype(mid, did, args) => Type::Datatype(
                mid,
                did,
                args.into_iter().map(Self::erase_type_params).collect(),
            ),
            other => other,
        }
    }

    /// Checked access to a source operand index.
    pub(crate) fn source(&self, sources: &[usize], i: usize) -> CompileResult<usize> {
        sources
            .get(i)
            .copied()
            .ok_or_else(|| CompileError::internal(format!("missing source operand at index {i}")))
    }

    /// Checked access to a destination operand index.
    pub(crate) fn destination(&self, destinations: &[usize], i: usize) -> CompileResult<usize> {
        destinations.get(i).copied().ok_or_else(|| {
            CompileError::internal(format!("missing destination operand at index {i}"))
        })
    }

    fn llvm_type_name(val: &BasicValueEnum<'_>) -> &'static str {
        match val {
            BasicValueEnum::IntValue(_) => "integer",
            BasicValueEnum::FloatValue(_) => "float",
            BasicValueEnum::PointerValue(_) => "pointer",
            BasicValueEnum::StructValue(_) => "struct",
            BasicValueEnum::ArrayValue(_) => "array",
            _ => "other",
        }
    }
}

#[cfg(test)]
mod tests {
    use move_model::ty::{PrimitiveType, Type};

    use super::FunctionState;

    #[test]
    fn erase_bare_type_param() {
        let ty = Type::TypeParameter(0);
        let erased = FunctionState::erase_type_params(ty);
        assert_eq!(erased, Type::Primitive(PrimitiveType::U64));
    }

    #[test]
    fn erase_nested_in_vector() {
        let ty = Type::Vector(Box::new(Type::TypeParameter(1)));
        let erased = FunctionState::erase_type_params(ty);
        assert_eq!(
            erased,
            Type::Vector(Box::new(Type::Primitive(PrimitiveType::U64)))
        );
    }

    #[test]
    fn erase_nested_in_reference() {
        let ty = Type::Reference(true, Box::new(Type::TypeParameter(0)));
        let erased = FunctionState::erase_type_params(ty);
        assert_eq!(
            erased,
            Type::Reference(true, Box::new(Type::Primitive(PrimitiveType::U64)))
        );
    }

    #[test]
    fn erase_deeply_nested() {
        // Vector<&mut TypeParameter(2)>
        let ty = Type::Vector(Box::new(Type::Reference(
            true,
            Box::new(Type::TypeParameter(2)),
        )));
        let erased = FunctionState::erase_type_params(ty);
        assert_eq!(
            erased,
            Type::Vector(Box::new(Type::Reference(
                true,
                Box::new(Type::Primitive(PrimitiveType::U64))
            )))
        );
    }

    #[test]
    fn preserve_concrete_types() {
        let u8_ty = Type::Primitive(PrimitiveType::U8);
        assert_eq!(FunctionState::erase_type_params(u8_ty.clone()), u8_ty);

        let vec_bool = Type::Vector(Box::new(Type::Primitive(PrimitiveType::Bool)));
        assert_eq!(
            FunctionState::erase_type_params(vec_bool.clone()),
            vec_bool,
        );
    }
}
