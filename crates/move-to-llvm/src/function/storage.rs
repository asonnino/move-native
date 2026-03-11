// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::types::BasicType;
use move_model::model::{DatatypeId, ModuleId};
use move_model::ty::Type;

use super::state::{CallSiteValueExt, FunctionState};
use crate::error::CompileResult;

/// Emits LLVM calls for Move global storage operations
/// (MoveTo, MoveFrom, Exists, BorrowGlobal, GetGlobal).
pub(crate) struct StorageEmitter<'a, 'b, 'ctx> {
    state: &'a FunctionState<'b, 'ctx>,
}

impl<'a, 'b, 'ctx> StorageEmitter<'a, 'b, 'ctx> {
    pub(super) fn new(state: &'a FunctionState<'b, 'ctx>) -> Self {
        Self { state }
    }

    pub(super) fn emit_move_to(
        &self,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        type_args: &[Type],
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = &self.state.ctx;
        let (symbol, datatype) =
            self.resolve_symbol("move_to", module_id, datatype_id, type_args)?;
        let parameter_type = self.state.lower_type(&datatype)?.into();
        let function_type = llvm
            .context
            .void_type()
            .fn_type(&[parameter_type, llvm.i256_type.into()], false);
        self.call_and_store(&symbol, function_type, destinations, sources)
    }

    pub(super) fn emit_move_from(
        &self,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        type_args: &[Type],
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = &self.state.ctx;
        let (symbol, datatype) =
            self.resolve_symbol("move_from", module_id, datatype_id, type_args)?;
        let return_type = self.state.lower_type(&datatype)?;
        let function_type = return_type.fn_type(&[llvm.i256_type.into()], false);
        self.call_and_store(&symbol, function_type, destinations, sources)
    }

    pub(super) fn emit_exists(
        &self,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        type_args: &[Type],
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = &self.state.ctx;
        let (symbol, _) = self.resolve_symbol("exists", module_id, datatype_id, type_args)?;
        let function_type = llvm.i8_type.fn_type(&[llvm.i256_type.into()], false);
        self.call_and_store(&symbol, function_type, destinations, sources)
    }

    pub(super) fn emit_borrow_global(
        &self,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        type_args: &[Type],
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = &self.state.ctx;
        let (symbol, _) =
            self.resolve_symbol("borrow_global", module_id, datatype_id, type_args)?;
        let function_type = llvm.ptr_type.fn_type(&[llvm.i256_type.into()], false);
        self.call_and_store(&symbol, function_type, destinations, sources)
    }

    pub(super) fn emit_get_global(
        &self,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        type_args: &[Type],
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = &self.state.ctx;
        let (symbol, datatype) =
            self.resolve_symbol("get_global", module_id, datatype_id, type_args)?;
        let return_type = self.state.lower_type(&datatype)?;
        let function_type = return_type.fn_type(&[llvm.i256_type.into()], false);
        self.call_and_store(&symbol, function_type, destinations, sources)
    }

    /// Resolve the runtime symbol for a storage operation on a concrete datatype.
    fn resolve_symbol(
        &self,
        operation_name: &str,
        module_id: ModuleId,
        datatype_id: DatatypeId,
        type_args: &[Type],
    ) -> CompileResult<(String, Type)> {
        let inst_args = self.state.instantiate_types(type_args);
        let datatype = Type::Datatype(module_id, datatype_id, inst_args);
        let mangled = self.state.mangle_type(&datatype)?;
        let symbol = format!("__move_rt_{operation_name}${mangled}");
        Ok((symbol, datatype))
    }

    /// Declare the extern, call it with loaded sources, and store the result.
    fn call_and_store(
        &self,
        symbol: &str,
        function_type: inkwell::types::FunctionType<'ctx>,
        destinations: &[usize],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = &self.state.ctx;
        let function_value = llvm.add_external_function(symbol, function_type);

        let args: Vec<_> = sources
            .iter()
            .map(|s| self.state.load_value(*s).map(|v| v.into()))
            .collect::<Result<_, _>>()?;

        let call = llvm.builder.build_call(function_value, &args, symbol)?;

        if !destinations.is_empty() {
            let ret_val = call.into_basic_value()?;
            self.state.store(destinations[0], ret_val)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use move_binary_format::file_format::{
        Bytecode, DatatypeHandleIndex, SignatureToken, StructDefinitionIndex,
    };

    use crate::compiler::Compiler;
    use crate::module::CompiledModuleBuilder;
    use crate::target::Target;

    #[test]
    fn exists_emits_runtime_call() {
        let module = CompiledModuleBuilder::coin()
            .function(
                "check_exists",
                vec![SignatureToken::Address],
                vec![SignatureToken::Bool],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::ExistsDeprecated(StructDefinitionIndex(0)),
                    Bytecode::Ret,
                ],
            )
            .build();

        let asm = Compiler::compile_module(&Target::host(), &module).unwrap();
        assert!(
            asm.contains("__move_rt_exists"),
            "missing __move_rt_exists call\n{asm}"
        );
    }

    #[test]
    fn move_from_emits_runtime_call() {
        let module = CompiledModuleBuilder::coin()
            .function(
                "take_coin",
                vec![SignatureToken::Address],
                vec![SignatureToken::Datatype(DatatypeHandleIndex(0))],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::MoveFromDeprecated(StructDefinitionIndex(0)),
                    Bytecode::Ret,
                ],
            )
            .build();

        let asm = Compiler::compile_module(&Target::host(), &module).unwrap();
        assert!(
            asm.contains("__move_rt_move_from"),
            "missing __move_rt_move_from call\n{asm}"
        );
    }

    #[test]
    fn move_to_emits_runtime_call() {
        let module = CompiledModuleBuilder::coin()
            .function(
                "publish_coin",
                vec![
                    SignatureToken::Datatype(DatatypeHandleIndex(0)),
                    SignatureToken::Signer,
                ],
                vec![],
                vec![],
                vec![
                    Bytecode::MoveLoc(1), // signer
                    Bytecode::MoveLoc(0), // coin
                    Bytecode::MoveToDeprecated(StructDefinitionIndex(0)),
                    Bytecode::Ret,
                ],
            )
            .build();

        let asm = Compiler::compile_module(&Target::host(), &module).unwrap();
        assert!(
            asm.contains("__move_rt_move_to"),
            "missing __move_rt_move_to call\n{asm}"
        );
    }

    #[test]
    fn borrow_global_emits_runtime_call() {
        let module = CompiledModuleBuilder::coin()
            .function(
                "borrow_coin",
                vec![SignatureToken::Address],
                vec![SignatureToken::Reference(Box::new(
                    SignatureToken::Datatype(DatatypeHandleIndex(0)),
                ))],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::ImmBorrowGlobalDeprecated(StructDefinitionIndex(0)),
                    Bytecode::Ret,
                ],
            )
            .build();

        let asm = Compiler::compile_module(&Target::host(), &module).unwrap();
        assert!(
            asm.contains("__move_rt_borrow_global"),
            "missing __move_rt_borrow_global call\n{asm}"
        );
    }
}
