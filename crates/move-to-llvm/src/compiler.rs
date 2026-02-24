// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::context::Context;
use inkwell::module::Linkage;
use inkwell::types::{BasicMetadataTypeEnum, BasicTypeEnum};
use inkwell::values::FunctionValue;
use move_binary_format::CompiledModule;
use move_model::model::FunctionEnv;
use move_model::ty::Type;
use move_stackless_bytecode::function_target::FunctionData;
use move_stackless_bytecode::stackless_bytecode_generator::StacklessBytecodeGenerator;

use crate::assembly::{Assembly, AssemblyBuilder};
use crate::context::LlvmContext;
use crate::error::{CompileError, CompileResult};
use crate::function::FunctionLowering;
use crate::mangle::Mangler;
use crate::types::TypeLowering;

/// Top-level compiler that owns the full Move -> AArch64 pipeline.
///
/// Bundles the LLVM context, the Move model environment (via `Mangler`),
/// and the code generator so that callers never need to thread
/// `(ctx, env)` pairs through every function call.
pub struct Compiler<'ctx> {
    pub(crate) ctx: LlvmContext<'ctx>,
    pub(crate) mangler: Mangler,
    asm_builder: AssemblyBuilder,
}

impl<'ctx> Compiler<'ctx> {
    /// Compile serialized Move bytecode to AArch64 assembly.
    pub fn compile(bytecode: &[u8]) -> CompileResult<Assembly> {
        let module = CompiledModule::deserialize_with_defaults(bytecode)
            .map_err(|e| CompileError::Deserialize(e.to_string()))?;
        Self::compile_module(&module)
    }

    /// Compile an already-deserialized Move module to AArch64 assembly.
    pub fn compile_module(module: &CompiledModule) -> CompileResult<Assembly> {
        Self::compile_module_with_deps(module, &[])
    }

    /// Compile a Move module to AArch64 assembly, with dependency modules
    /// visible for resolving cross-module function signatures.
    pub fn compile_module_with_deps(
        module: &CompiledModule,
        deps: &[CompiledModule],
    ) -> CompileResult<Assembly> {
        let context = Context::create();
        Self::compile_with_context(&context, module, deps)
    }

    /// Compile using an externally-owned LLVM context.
    ///
    /// This separate method lets the static entry points create the `Context`
    /// on their stack frame so that `Compiler<'ctx>` can borrow it without
    /// lifetime issues.
    fn compile_with_context(
        context: &Context,
        module: &CompiledModule,
        deps: &[CompiledModule],
    ) -> CompileResult<Assembly> {
        let compiler = Compiler::new(context, module, deps)?;
        compiler.run()
    }

    fn new(
        context: &'ctx Context,
        module: &CompiledModule,
        deps: &[CompiledModule],
    ) -> CompileResult<Self> {
        let ctx = LlvmContext::new(context, "move_module");
        let asm_builder = AssemblyBuilder::new()?;

        let all_modules: Vec<&CompiledModule> =
            deps.iter().chain(std::iter::once(module)).collect();
        let env = move_model::run_bytecode_model_builder(all_modules)
            .map_err(|e| CompileError::ModelBuilder(e.to_string()))?;

        Ok(Self {
            ctx,
            mangler: Mangler::new(env),
            asm_builder,
        })
    }

    fn run(&self) -> CompileResult<Assembly> {
        let target_module_env = self.mangler.env().get_modules().last().unwrap();

        let funcs: Vec<_> = target_module_env
            .into_functions()
            .filter(|f| !f.is_native() && f.get_type_parameter_count() == 0)
            .map(|func_env| {
                let generator = StacklessBytecodeGenerator::new(&func_env);
                let func_data = generator.generate_function();
                (func_env, func_data)
            })
            .collect();

        // Pass 1: declare all functions (so callees are visible).
        let declarations: Vec<_> = funcs
            .iter()
            .map(|(func_env, func_data)| self.declare_function(func_env, func_data))
            .collect::<Result<_, _>>()?;

        // Pass 2: compile function bodies.
        for ((func_env, func_data), function) in funcs.iter().zip(declarations) {
            self.compile_function(function, func_env, func_data)?;
        }

        self.asm_builder.optimize(&self.ctx.module)?;
        let mut asm = self.asm_builder.emit_assembly(&self.ctx.module)?;
        asm.add_symbol_aliases();
        Ok(asm)
    }

    /// Declare an LLVM function (signature only, no body) for the given Move function.
    pub(crate) fn declare_function(
        &self,
        func_env: &FunctionEnv<'_>,
        func_data: &FunctionData,
    ) -> CompileResult<FunctionValue<'ctx>> {
        let name = func_env
            .module_env
            .env
            .symbol_pool()
            .string(func_env.get_name());
        let param_count = func_env.get_parameter_count();

        let param_llvm_types: Vec<_> = func_data.local_types[..param_count]
            .iter()
            .map(|ty| self.lower_type(ty).map(|t| t.into()))
            .collect::<Result<_, _>>()?;

        let fn_type = self.build_fn_type(&func_data.return_types, &param_llvm_types)?;
        Ok(self.ctx.module.add_function(&name, fn_type, None))
    }

    /// Compile the body of an already-declared LLVM function.
    pub(crate) fn compile_function(
        &self,
        function: FunctionValue<'ctx>,
        func_env: &FunctionEnv<'_>,
        func_data: &FunctionData,
    ) -> CompileResult<()> {
        let param_count = func_env.get_parameter_count();
        let lowering = FunctionLowering::new(self, function, param_count, func_data, Vec::new())?;
        lowering.lower_code(func_data)?;
        Ok(())
    }

    /// Create a `TypeLowering` view for this compiler.
    pub(crate) fn types(&self) -> TypeLowering<'_, 'ctx> {
        TypeLowering::new(&self.ctx, &self.mangler)
    }

    /// Convenience: lower a Move type to an LLVM type.
    pub(crate) fn lower_type(&self, ty: &Type) -> CompileResult<BasicTypeEnum<'ctx>> {
        self.types().lower_type(ty)
    }

    /// Convenience: build an LLVM function type from Move return types and LLVM param types.
    pub(crate) fn build_fn_type(
        &self,
        ret_types: &[Type],
        param_types: &[BasicMetadataTypeEnum<'ctx>],
    ) -> CompileResult<inkwell::types::FunctionType<'ctx>> {
        self.types().build_fn_type(ret_types, param_types)
    }

    /// Convenience: mangle a Move type.
    pub(crate) fn mangle_type(&self, ty: &Type) -> String {
        self.mangler.mangle_type(ty)
    }

    /// Convenience: mangle type arguments.
    pub(crate) fn mangle_type_args(&self, type_args: &[Type]) -> String {
        self.mangler.mangle_type_args(type_args)
    }

    /// Convenience: mangle a native symbol.
    pub(crate) fn mangle_native_symbol(
        &self,
        callee_env: &FunctionEnv<'_>,
        type_args: &[Type],
    ) -> String {
        self.mangler.mangle_native_symbol(callee_env, type_args)
    }

    /// Get an existing function from the module, or declare it as an external.
    pub(crate) fn get_or_declare_extern(
        &self,
        name: &str,
        fn_type: inkwell::types::FunctionType<'ctx>,
    ) -> FunctionValue<'ctx> {
        match self.ctx.module.get_function(name) {
            Some(f) => f,
            None => self
                .ctx
                .module
                .add_function(name, fn_type, Some(Linkage::External)),
        }
    }
}
