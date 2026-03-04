// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::values::FunctionValue;
use move_model::model::{FunId, ModuleId};
use move_model::ty::Type;
use move_stackless_bytecode::stackless_bytecode_generator::StacklessBytecodeGenerator;

use super::FunctionLowering;
use super::state::FunctionState;
use crate::error::{CompileError, CompileResult};

/// Emits LLVM call instructions for Move function calls.
///
/// Handles three cases: native functions (extern declarations),
/// generic functions (monomorphization), and non-generic calls.
pub(crate) struct CallEmitter<'a, 'b, 'ctx> {
    state: &'a FunctionState<'b, 'ctx>,
}

impl<'a, 'b, 'ctx> CallEmitter<'a, 'b, 'ctx> {
    pub fn new(state: &'a FunctionState<'b, 'ctx>) -> Self {
        Self { state }
    }

    pub fn emit(
        &self,
        destinations: &[usize],
        module_id: ModuleId,
        function_id: FunId,
        type_args: &[Type],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = &self.state.ctx;
        let callee_env = self
            .state
            .ctx
            .env()
            .get_module(module_id)
            .into_function(function_id);

        let (callee_fn, call_name) = if callee_env.is_native() {
            self.emit_native(&callee_env, type_args)?
        } else if !type_args.is_empty() {
            self.emit_generic(&callee_env, type_args)?
        } else {
            self.emit_non_generic(&callee_env)?
        };

        let args: Vec<_> = sources
            .iter()
            .map(|s| self.state.load_value(*s).map(|v| v.into()))
            .collect::<Result<_, _>>()?;

        let call = llvm.builder.build_call(callee_fn, &args, &call_name)?;

        if !destinations.is_empty() {
            let ret_val = match call.try_as_basic_value() {
                inkwell::values::ValueKind::Basic(v) => v,
                _ => panic!("expected non-void return from callee"),
            };
            if destinations.len() == 1 {
                self.state.store(destinations[0], ret_val)?;
            } else {
                // Multi-return: unpack struct into individual destinations
                let struct_val = ret_val.into_struct_value();
                for (i, destination) in destinations.iter().enumerate() {
                    let field = llvm.builder.build_extract_value(
                        struct_val,
                        i as u32,
                        &format!("call_ret_{i}"),
                    )?;
                    self.state.store(*destination, field)?;
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
        let llvm = &self.state.ctx;
        let mangled = self.state.mangle_native_symbol(callee_env, type_args)?;
        let inst_params: Vec<Type> = callee_env
            .get_parameter_types()
            .iter()
            .map(|t: &Type| t.instantiate(type_args))
            .collect();
        let inst_rets: Vec<Type> = callee_env
            .get_return_types()
            .iter()
            .map(|t: &Type| t.instantiate(type_args))
            .collect();
        let fn_type = self.state.lower_function_type(&inst_params, &inst_rets)?;
        let f = llvm.add_external_function(&mangled, fn_type);
        Ok((f, mangled))
    }

    /// Monomorphize: compile a specialized copy of the callee
    /// with TypeParameters replaced by concrete types.
    fn emit_generic(
        &self,
        callee_env: &move_model::model::FunctionEnv<'_>,
        type_args: &[Type],
    ) -> CompileResult<(FunctionValue<'ctx>, String)> {
        let llvm = &self.state.ctx;
        let inst_args = self.state.inst_types(type_args);
        let callee_name = callee_env.get_name_str();
        let args = self.state.mangle_type_args(&inst_args)?;
        let mangled = format!("{callee_name}${args}");
        let f = match llvm.get_function(&mangled) {
            Some(f) => f,
            None => {
                let inst_params: Vec<Type> = callee_env
                    .get_parameter_types()
                    .iter()
                    .map(|t: &Type| t.instantiate(&inst_args))
                    .collect();
                let inst_rets: Vec<Type> = callee_env
                    .get_return_types()
                    .iter()
                    .map(|t: &Type| t.instantiate(&inst_args))
                    .collect();
                let fn_type = self.state.lower_function_type(&inst_params, &inst_rets)?;
                let function = llvm.add_function(&mangled, fn_type);

                let saved_block = llvm
                    .builder
                    .get_insert_block()
                    .ok_or(CompileError::llvm("no insert block"))?;

                let generator = StacklessBytecodeGenerator::new(callee_env);
                let func_data = generator.generate_function();
                let param_count = callee_env.get_parameter_count();
                let callee_lowering = FunctionLowering::new(
                    self.state.ctx,
                    function,
                    param_count,
                    &func_data,
                    inst_args,
                )?;
                callee_lowering.lower_function(&func_data)?;

                llvm.builder.position_at_end(saved_block);
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
        let llvm = &self.state.ctx;
        let callee_name = callee_env.get_name_str();
        let f = match llvm.get_function(&callee_name) {
            Some(f) => f,
            None => {
                let fn_type = self.state.lower_function_type(
                    &callee_env.get_parameter_types(),
                    &callee_env.get_return_types(),
                )?;
                llvm.add_external_function(&callee_name, fn_type)
            }
        };
        Ok((f, callee_name))
    }
}
