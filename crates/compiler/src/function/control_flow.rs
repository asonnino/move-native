// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::IntPredicate;
use inkwell::types::BasicTypeEnum;
use move_model::ty::Type;
use move_stackless_bytecode::stackless_bytecode::Bytecode;

use super::state::FunctionState;
use crate::error::{CompileError, CompileResult, to_field_index};

/// Emits LLVM IR for control-flow bytecodes
/// (Ret, Label, Jump, Branch, Abort).
pub(crate) struct ControlFlowEmitter<'a, 'b, 'ctx> {
    state: &'a FunctionState<'b, 'ctx>,
}

impl<'a, 'b, 'ctx> ControlFlowEmitter<'a, 'b, 'ctx> {
    pub(super) fn new(state: &'a FunctionState<'b, 'ctx>) -> Self {
        Self { state }
    }

    pub(super) fn emit(&self, byte_code: &Bytecode) -> CompileResult<()> {
        let llvm = self.state.ctx;
        match byte_code {
            Bytecode::Ret(_, returns) => {
                if returns.is_empty() {
                    llvm.builder.build_return(None)?;
                } else if returns.len() == 1 {
                    let val = self.state.load_value(returns[0])?;
                    llvm.builder.build_return(Some(&val))?;
                } else {
                    // Multi-return: pack values into an anonymous struct
                    let return_types: Vec<BasicTypeEnum<'ctx>> = returns
                        .iter()
                        .map(|r| Ok(self.state.get_local(*r)?.llvm_ty))
                        .collect::<CompileResult<_>>()?;
                    let return_struct_type = llvm.context.struct_type(&return_types, false);
                    let mut struct_value = return_struct_type.get_undef();
                    for (i, r) in returns.iter().enumerate() {
                        let val = self.state.load_value(*r)?;
                        struct_value = llvm
                            .builder
                            .build_insert_value(struct_value, val, to_field_index(i)?, &format!("ret_{i}"))?
                            .into_struct_value();
                    }
                    llvm.builder.build_return(Some(&struct_value))?;
                }
            }
            Bytecode::Label(_, label) => {
                let block = self.state.get_label_block(label)?;
                // Add fallthrough branch if current block has no terminator
                let current = llvm
                    .builder
                    .get_insert_block()
                    .ok_or(CompileError::llvm("no insert block"))?;
                if current.get_terminator().is_none() {
                    llvm.builder.build_unconditional_branch(block)?;
                }
                llvm.builder.position_at_end(block);
            }
            Bytecode::Jump(_, label) => {
                let block = self.state.get_label_block(label)?;
                llvm.builder.build_unconditional_branch(block)?;
            }
            Bytecode::Branch(_, then_label, else_label, cond) => {
                let cond_val = self.state.load_int(*cond)?;
                let zero = cond_val.get_type().const_zero();
                let compare =
                    llvm.builder
                        .build_int_compare(IntPredicate::NE, cond_val, zero, "cond")?;
                let then_block = self.state.get_label_block(then_label)?;
                let else_block = self.state.get_label_block(else_label)?;
                llvm.builder
                    .build_conditional_branch(compare, then_block, else_block)?;
            }
            Bytecode::VariantSwitch(_, source, labels) => {
                let tag = match &self.state.get_local(*source)?.mty {
                    Type::Reference(_, inner) => match inner.as_ref() {
                        Type::Datatype(..) => {
                            let enum_ptr = self.state.load_pointer(*source)?;
                            let pointee = self.state.pointee_type(*source)?;
                            let BasicTypeEnum::StructType(enum_type) = pointee else {
                                return Err(CompileError::TypeMismatch(format!(
                                    "expected enum reference for VariantSwitch, got {pointee:?}"
                                )));
                            };
                            let tag_ptr = llvm.builder.build_struct_gep(
                                enum_type,
                                enum_ptr,
                                0,
                                "variant_tag_ptr",
                            )?;
                            let tag_type =
                                enum_type.get_field_type_at_index(0).ok_or_else(|| {
                                    CompileError::InvalidReference(
                                        "missing enum tag field for VariantSwitch".into(),
                                    )
                                })?;
                            llvm.builder
                                .build_load(tag_type, tag_ptr, "variant_tag")?
                                .into_int_value()
                        }
                        other => return Err(CompileError::unsupported(other)),
                    },
                    _ => self.state.load_struct(*source).and_then(|enum_value| {
                        llvm.builder
                            .build_extract_value(enum_value, 0, "variant_tag")
                            .map(|value| value.into_int_value())
                            .map_err(Into::into)
                    })?,
                };
                let default_block =
                    self.state.get_label_block(labels.last().ok_or_else(|| {
                        CompileError::InvalidReference("empty VariantSwitch".into())
                    })?)?;
                let cases: Vec<_> = labels
                    .iter()
                    .enumerate()
                    .map(|(tag_value, label)| {
                        let block = self.state.get_label_block(label)?;
                        let tag_const = tag.get_type().const_int(tag_value as u64, false);
                        Ok((tag_const, block))
                    })
                    .collect::<CompileResult<_>>()?;
                llvm.builder.build_switch(tag, default_block, &cases)?;
            }
            Bytecode::Abort(_, code_idx) => {
                let code = self.state.load_value(*code_idx)?;
                let abort_fn = self.state.declare_external(
                    "__move_rt_abort",
                    llvm.context
                        .void_type()
                        .fn_type(&[llvm.i64_type.into()], false),
                );
                llvm.builder.build_call(abort_fn, &[code.into()], "abort")?;
                llvm.builder.build_unreachable()?;
            }
            _ => unreachable!("non-control-flow bytecode routed to ControlFlowEmitter"),
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use move_binary_format::file_format::{Bytecode, SignatureToken};

    use crate::compiler::Compiler;
    use crate::module::CompiledModuleBuilder;
    use crate::target::Target;

    #[test]
    fn ret_void() {
        let module = CompiledModuleBuilder::new()
            .function("noop", vec![], vec![], vec![], vec![Bytecode::Ret])
            .build();

        let asm = Compiler::compile_module(&Target::host(), &module).unwrap();
        assert!(asm.contains("0x0_M_noop"), "missing 'noop' symbol\n{asm}");
        assert!(asm.contains("ret"), "missing 'ret' instruction\n{asm}");
    }

    #[test]
    fn ret_single_value() {
        let module = CompiledModuleBuilder::new()
            .function(
                "identity",
                vec![SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![],
                vec![Bytecode::CopyLoc(0), Bytecode::Ret],
            )
            .build();

        let asm = Compiler::compile_module(&Target::host(), &module).unwrap();
        assert!(
            asm.contains("0x0_M_identity"),
            "missing 'identity' symbol\n{asm}"
        );
        assert!(asm.contains("ret"), "missing 'ret' instruction\n{asm}");
    }

    #[test]
    fn ret_multi_value() {
        let module = CompiledModuleBuilder::new()
            .function(
                "swap",
                vec![SignatureToken::U64, SignatureToken::U64],
                vec![SignatureToken::U64, SignatureToken::U64],
                vec![],
                vec![Bytecode::CopyLoc(1), Bytecode::CopyLoc(0), Bytecode::Ret],
            )
            .build();

        let asm = Compiler::compile_module(&Target::host(), &module).unwrap();
        assert!(asm.contains("0x0_M_swap"), "missing 'swap' symbol\n{asm}");
        assert!(asm.contains("ret"), "missing 'ret' instruction\n{asm}");
    }

    #[test]
    fn branch_and_jump() {
        let module = CompiledModuleBuilder::new()
            .function(
                "sum_to_n",
                vec![SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![SignatureToken::U64, SignatureToken::U64],
                vec![
                    Bytecode::LdU64(0),
                    Bytecode::StLoc(1), // sum = 0
                    Bytecode::LdU64(0),
                    Bytecode::StLoc(2), // i = 0
                    // LOOP:
                    Bytecode::CopyLoc(2),
                    Bytecode::CopyLoc(0),
                    Bytecode::Lt,
                    Bytecode::BrFalse(17), // -> END
                    // body
                    Bytecode::CopyLoc(1),
                    Bytecode::CopyLoc(2),
                    Bytecode::Add,
                    Bytecode::StLoc(1), // sum += i
                    Bytecode::CopyLoc(2),
                    Bytecode::LdU64(1),
                    Bytecode::Add,
                    Bytecode::StLoc(2),  // i += 1
                    Bytecode::Branch(4), // -> LOOP
                    // END:
                    Bytecode::MoveLoc(1),
                    Bytecode::Ret,
                ],
            )
            .build();

        let asm = Compiler::compile_module(&Target::host(), &module).unwrap();
        assert!(
            asm.contains("0x0_M_sum_to_n"),
            "missing 'sum_to_n' symbol\n{asm}"
        );
        assert!(asm.contains("b."), "missing conditional branch\n{asm}");
    }

    #[test]
    fn abort() {
        let module = CompiledModuleBuilder::new()
            .function(
                "abort_42",
                vec![],
                vec![],
                vec![SignatureToken::U64],
                vec![
                    Bytecode::LdU64(42),
                    Bytecode::StLoc(0),
                    Bytecode::MoveLoc(0),
                    Bytecode::Abort,
                ],
            )
            .build();

        let asm = Compiler::compile_module(&Target::host(), &module).unwrap();
        assert!(
            asm.contains("0x0_M_abort_42"),
            "missing 'abort_42' symbol\n{asm}"
        );
        assert!(
            asm.contains("__move_rt_abort"),
            "missing '__move_rt_abort' call\n{asm}"
        );
    }
}
