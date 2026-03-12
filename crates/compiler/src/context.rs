// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::AddressSpace;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{FunctionType, IntType, PointerType};
use inkwell::values::FunctionValue;
use move_binary_format::CompiledModule;
use move_model::model::{
    DatatypeId, FunId, FunctionEnv, GlobalEnv, ModuleEnv, ModuleId, StructEnv,
};
use move_model::ty::Type;

use crate::error::{CompileError, CompileResult};
use crate::mangle::Mangler;

/// Wraps the LLVM Context, Module, and Builder for a single compilation unit.
///
/// Also owns the Move `GlobalEnv` (semantic model) so that all central
/// infrastructure lives in one place.
pub(crate) struct LlvmContext<'ctx> {
    env: GlobalEnv,
    pub(crate) context: &'ctx Context,
    pub(crate) module: Module<'ctx>,
    pub(crate) builder: Builder<'ctx>,
    // Cached integer types
    pub(crate) i8_type: IntType<'ctx>,
    pub(crate) i16_type: IntType<'ctx>,
    pub(crate) i32_type: IntType<'ctx>,
    pub(crate) i64_type: IntType<'ctx>,
    pub(crate) i128_type: IntType<'ctx>,
    pub(crate) i256_type: IntType<'ctx>,
    pub(crate) ptr_type: PointerType<'ctx>,
}

impl<'ctx> LlvmContext<'ctx> {
    pub(crate) fn new(
        context: &'ctx Context,
        module: &CompiledModule,
        dependencies: &[CompiledModule],
    ) -> CompileResult<Self> {
        Self::validate_dependencies(module, dependencies)?;

        let all_modules: Vec<&CompiledModule> =
            dependencies.iter().chain(std::iter::once(module)).collect();
        let env = move_model::run_bytecode_model_builder(all_modules)
            .map_err(|e| CompileError::model_builder(e.to_string()))?;
        let module_name = env
            .get_modules()
            .last()
            .expect("env always contains at least the target module")
            .get_full_name_str();
        let llvm_module = context.create_module(&module_name);
        let builder = context.create_builder();

        Ok(Self {
            env,
            context,
            module: llvm_module,
            builder,
            i8_type: context.i8_type(),
            i16_type: context.i16_type(),
            i32_type: context.i32_type(),
            i64_type: context.i64_type(),
            i128_type: context.i128_type(),
            i256_type: context.custom_width_int_type(256),
            ptr_type: context.ptr_type(AddressSpace::default()),
        })
    }

    /// Verify that all modules referenced by `module` are present in `dependencies`.
    fn validate_dependencies(
        module: &CompiledModule,
        dependencies: &[CompiledModule],
    ) -> CompileResult<()> {
        let self_id = module.self_id();
        let dependency_ids: std::collections::HashSet<_> =
            dependencies.iter().map(|d| d.self_id()).collect();

        for handle in &module.module_handles {
            let id = module.module_id_for_handle(handle);
            if id == self_id {
                continue;
            }
            if !dependency_ids.contains(&id) {
                return Err(CompileError::MissingDependency(format!("{id}")));
            }
        }
        Ok(())
    }

    /// Create a minimal `LlvmContext` with an empty `GlobalEnv` for unit testing.
    ///
    /// Leaks the LLVM `Context` so the returned value is `'static` — fine for tests.
    /// Sufficient for code paths that don't access the Move environment
    /// (primitives, references, vectors, etc.).
    #[cfg(test)]
    pub(crate) fn new_for_test() -> LlvmContext<'static> {
        let context: &'static Context = Box::leak(Box::new(Context::create()));
        let llvm_module = context.create_module("test");
        let builder = context.create_builder();
        LlvmContext {
            env: GlobalEnv::new(),
            context,
            module: llvm_module,
            builder,
            i8_type: context.i8_type(),
            i16_type: context.i16_type(),
            i32_type: context.i32_type(),
            i64_type: context.i64_type(),
            i128_type: context.i128_type(),
            i256_type: context.custom_width_int_type(256),
            ptr_type: context.ptr_type(AddressSpace::default()),
        }
    }

    /// Look up a struct definition by module and datatype ID.
    pub(crate) fn get_struct_env(
        &self,
        module_id: ModuleId,
        datatype_id: DatatypeId,
    ) -> StructEnv<'_> {
        self.env.get_module(module_id).into_struct(datatype_id)
    }

    /// Look up a function definition by module and function ID.
    pub(crate) fn get_function_env(
        &self,
        module_id: ModuleId,
        function_id: FunId,
    ) -> FunctionEnv<'_> {
        self.env.get_module(module_id).into_function(function_id)
    }

    /// The module being compiled (always the last one added to the environment).
    pub(crate) fn target_module(&self) -> ModuleEnv<'_> {
        self.env
            .get_modules()
            .last()
            .expect("env always contains at least the target module")
    }

    /// Look up an already-declared function by name.
    pub(crate) fn get_function(&self, name: &str) -> Option<FunctionValue<'ctx>> {
        self.module.get_function(name)
    }

    /// Add a function definition (with body) to this module.
    pub(crate) fn add_function(
        &self,
        name: &str,
        function_type: FunctionType<'ctx>,
    ) -> FunctionValue<'ctx> {
        self.module.add_function(name, function_type, None)
    }

    /// Declare an external function (defined elsewhere, resolved at link time), idempotent.
    pub(crate) fn add_external_function(
        &self,
        name: &str,
        function_type: FunctionType<'ctx>,
    ) -> FunctionValue<'ctx> {
        self.module.get_function(name).unwrap_or_else(|| {
            self.module
                .add_function(name, function_type, Some(Linkage::External))
        })
    }

    /// Mangle a Move type into a symbol-safe string.
    pub(crate) fn mangle_type(&self, ty: &Type) -> CompileResult<String> {
        Mangler::new(&self.env).mangle_type(ty)
    }

    /// Mangle type arguments into a `$`-separated string.
    pub(crate) fn mangle_type_args(&self, type_args: &[Type]) -> CompileResult<String> {
        Mangler::new(&self.env).mangle_type_args(type_args)
    }

    /// Build the mangled symbol name for a native function call.
    pub(crate) fn mangle_native_symbol(
        &self,
        callee_env: &FunctionEnv<'_>,
        type_args: &[Type],
    ) -> CompileResult<String> {
        Mangler::new(&self.env).mangle_native_symbol(callee_env, type_args)
    }
}
