// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::module::Linkage;
use inkwell::values::FunctionValue;
use move_model::model::{FunId, ModuleId};
use move_model::ty::Type;
use move_stackless_bytecode::stackless_bytecode_generator::StacklessBytecodeGenerator;

use super::FunctionLowering;
use crate::error::CompileResult;

/// Emits LLVM call instructions for Move function calls.
///
/// Handles three cases: native functions (extern declarations),
/// generic functions (monomorphization), and non-generic calls.
pub(crate) struct CallEmitter<'a, 'b, 'ctx> {
    fl: &'a FunctionLowering<'b, 'ctx>,
}

impl<'a, 'b, 'ctx> CallEmitter<'a, 'b, 'ctx> {
    pub fn new(fl: &'a FunctionLowering<'b, 'ctx>) -> Self {
        Self { fl }
    }

    pub fn emit(
        &self,
        dsts: &[usize],
        module_id: ModuleId,
        fun_id: FunId,
        type_args: &[Type],
        srcs: &[usize],
    ) -> CompileResult<()> {
        let ctx = &self.fl.compiler.ctx;
        let callee_env = self
            .fl
            .compiler
            .mangler
            .env()
            .get_module(module_id)
            .into_function(fun_id);

        let (callee_fn, call_name) = if callee_env.is_native() {
            self.emit_native(&callee_env, type_args)?
        } else if !type_args.is_empty() {
            self.emit_generic(&callee_env, type_args)?
        } else {
            self.emit_non_generic(&callee_env)?
        };

        let args: Vec<_> = srcs
            .iter()
            .map(|s| self.fl.load_value(*s).map(|v| v.into()))
            .collect::<Result<_, _>>()?;

        let call = ctx
            .builder
            .build_call(callee_fn, &args, &call_name)
            .unwrap();

        if !dsts.is_empty() {
            let ret_val = match call.try_as_basic_value() {
                inkwell::values::ValueKind::Basic(v) => v,
                _ => panic!("expected non-void return from callee"),
            };
            if dsts.len() == 1 {
                self.fl.store(dsts[0], ret_val);
            } else {
                // Multi-return: unpack struct into individual destinations
                let struct_val = ret_val.into_struct_value();
                for (i, dst) in dsts.iter().enumerate() {
                    let field = ctx
                        .builder
                        .build_extract_value(struct_val, i as u32, &format!("call_ret_{i}"))
                        .unwrap();
                    self.fl.store(*dst, field);
                }
            }
        }
        Ok(())
    }

    /// Native function: declare as extern with monomorphized symbol.
    fn emit_native(
        &self,
        callee_env: &move_model::model::FunctionEnv<'_>,
        type_args: &[Type],
    ) -> CompileResult<(FunctionValue<'ctx>, String)> {
        let ctx = &self.fl.compiler.ctx;
        let mangled = self.fl.compiler.mangle_native_symbol(callee_env, type_args);
        let f = match ctx.module.get_function(&mangled) {
            Some(f) => f,
            None => {
                let param_types: Vec<_> = callee_env
                    .get_parameter_types()
                    .iter()
                    .map(|t: &Type| t.instantiate(type_args))
                    .map(|t| self.fl.compiler.lower_type(&t).map(|lt| lt.into()))
                    .collect::<Result<_, _>>()?;
                let ret_types: Vec<Type> = callee_env
                    .get_return_types()
                    .iter()
                    .map(|t: &Type| t.instantiate(type_args))
                    .collect();
                let fn_type = self.fl.compiler.build_fn_type(&ret_types, &param_types)?;
                ctx.module
                    .add_function(&mangled, fn_type, Some(Linkage::External))
            }
        };
        Ok((f, mangled))
    }

    /// Monomorphize: compile a specialized copy of the callee
    /// with TypeParameters replaced by concrete types.
    fn emit_generic(
        &self,
        callee_env: &move_model::model::FunctionEnv<'_>,
        type_args: &[Type],
    ) -> CompileResult<(FunctionValue<'ctx>, String)> {
        let ctx = &self.fl.compiler.ctx;
        let inst_args = self.fl.inst_types(type_args);
        let callee_name = callee_env.get_name_str();
        let mangled = format!(
            "{}${}",
            callee_name,
            self.fl.compiler.mangle_type_args(&inst_args)
        );
        let f = match ctx.module.get_function(&mangled) {
            Some(f) => f,
            None => {
                let param_types: Vec<_> = callee_env
                    .get_parameter_types()
                    .iter()
                    .map(|t: &Type| t.instantiate(&inst_args))
                    .map(|t| self.fl.compiler.lower_type(&t).map(|lt| lt.into()))
                    .collect::<Result<_, _>>()?;
                let ret_types: Vec<Type> = callee_env
                    .get_return_types()
                    .iter()
                    .map(|t: &Type| t.instantiate(&inst_args))
                    .collect();
                let fn_type = self.fl.compiler.build_fn_type(&ret_types, &param_types)?;
                let function = ctx.module.add_function(&mangled, fn_type, None);

                let saved_block = ctx.builder.get_insert_block().unwrap();

                let generator = StacklessBytecodeGenerator::new(callee_env);
                let func_data = generator.generate_function();
                let param_count = callee_env.get_parameter_count();
                let callee_lowering = FunctionLowering::new(
                    self.fl.compiler,
                    function,
                    param_count,
                    &func_data,
                    inst_args,
                )?;
                callee_lowering.lower_code(&func_data)?;

                ctx.builder.position_at_end(saved_block);
                function
            }
        };
        Ok((f, mangled))
    }

    /// Non-generic, non-native: look up in current LLVM module first
    /// (intra-module calls declared in pass 1), then fall back to an
    /// extern declaration for cross-module calls resolved at link time.
    fn emit_non_generic(
        &self,
        callee_env: &move_model::model::FunctionEnv<'_>,
    ) -> CompileResult<(FunctionValue<'ctx>, String)> {
        let ctx = &self.fl.compiler.ctx;
        let callee_name = callee_env.get_name_str();
        let f = match ctx.module.get_function(&callee_name) {
            Some(f) => f,
            None => {
                let param_types: Vec<_> = callee_env
                    .get_parameter_types()
                    .iter()
                    .map(|t| self.fl.compiler.lower_type(t).map(|lt| lt.into()))
                    .collect::<Result<_, _>>()?;
                let ret_types = callee_env.get_return_types();
                let fn_type = self.fl.compiler.build_fn_type(&ret_types, &param_types)?;
                ctx.module
                    .add_function(&callee_name, fn_type, Some(Linkage::External))
            }
        };
        Ok((f, callee_name))
    }
}
