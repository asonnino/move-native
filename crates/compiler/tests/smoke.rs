// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the Move-to-LLVM compiler.

use compiler::Target;
use compiler::module::CompiledModuleBuilder;
use move_binary_format::file_format::{Bytecode, FunctionHandleIndex, SignatureToken};
use move_core_types::account_address::AccountAddress;
use rstest::rstest;

#[rstest]
#[case::aarch64(Target::Aarch64)]
#[case::riscv64(Target::Riscv64)]
fn kitchen_sink_compiles(#[case] target: Target) {
    let (module, deps) = CompiledModuleBuilder::kitchen_sink();
    let asm = compiler::compile_module_with_deps(&target, &module, &deps).unwrap();

    // Verify all function symbols are present (target-independent).
    for name in &[
        "_mv_0x0_M_make_point",
        "_mv_0x0_M_sum_point",
        "_mv_0x0_M_forty_two",
        "_mv_0x0_M_low_byte",
        "_mv_0x0_M_cast_widths",
        "_mv_0x0_M_add_u16",
        "_mv_0x0_M_add_u32",
        "_mv_0x0_M_add_u128",
        "_mv_0x0_M_add_u256",
        "_mv_0x0_M_discard",
        "_mv_0x0_M_swap_fields",
        "_mv_0x0_M_freeze_and_read",
        "_mv_0x0_M_read_x",
        "_mv_0x0_M_swap_u64",
        "_mv_0x0_M_checked_sub",
        "_mv_0x0_M_round_trip",
        "_mv_0x0_M_identity",
        "_mv_0x0_M_call_identity",
        "_mv_0x0_M_sum_loop",
        "_mv_0x0_M_integration_test",
        "_mv_0x0_M_call_double",
        "_mv_0x0_M_test_vec",
        "_mv_0x0_M_eq_points",
        "_mv_0x0_M_eq_refs",
        "_mv_0x0_M_neq_u64",
        "_mv_0x0_M_phantom_read_x",
        "_mv_0x0_M_phantom_proxy",
    ] {
        assert!(
            asm.contains(name),
            "assembly should contain '{name}'\nassembly:\n{asm}"
        );
    }

    assert!(
        asm.contains("\tret"),
        "should contain function returns (ret)"
    );
    assert!(
        asm.contains("_mv_0x0_M_identity$u64"),
        "should contain monomorphized generic (identity$u64)"
    );
    assert!(
        asm.contains("_mv_0x0_M_phantom_read_x$u64"),
        "should contain erased phantom monomorphization (phantom_read_x$u64)\nassembly:\n{asm}"
    );
    assert!(
        asm.contains("__move_rt_abort"),
        "should contain abort runtime call"
    );
    assert!(
        asm.contains("__move_rt_arithmetic_error"),
        "should contain arithmetic error runtime call"
    );

    for symbol in &[
        "__move_rt_0x1_vector_empty",
        "__move_rt_0x1_vector_push_back",
        "__move_rt_0x1_vector_pop_back",
        "__move_rt_0x1_vector_destroy_empty",
    ] {
        assert!(
            asm.contains(symbol),
            "assembly should contain '{symbol}'\nassembly:\n{asm}"
        );
    }

    // Architecture-specific instruction patterns.
    match target {
        Target::Aarch64 => {
            assert!(asm.contains("\tbl\t"), "should contain function calls (bl)");
            assert!(
                asm.contains("\tb."),
                "should contain conditional branches (b.cond)"
            );
            // Cross-module call to Dep::double. Mach-O prepends an extra `_` to
            // symbols, so substring-match the ELF (single-underscore) form.
            assert!(
                asm.contains("_mv_0x0_Dep_double"),
                "should reference external symbol _mv_0x0_Dep_double\nassembly:\n{asm}"
            );
        }
        Target::Riscv64 => {
            assert!(
                asm.contains("_mv_0x0_M_make_point"),
                "should contain symbol _mv_0x0_M_make_point\nassembly:\n{asm}"
            );
        }
        _ => {}
    }
}

#[rstest]
#[case::aarch64(Target::Aarch64)]
#[case::riscv64(Target::Riscv64)]
fn same_name_cross_module_no_collision(#[case] target: Target) {
    // Build dep module: 0x0::Dep with function "double"
    let dep = CompiledModuleBuilder::named("Dep", AccountAddress::ZERO)
        .function(
            "double",
            vec![SignatureToken::U64],
            vec![SignatureToken::U64],
            vec![],
            vec![
                Bytecode::CopyLoc(0),
                Bytecode::CopyLoc(0),
                Bytecode::Add,
                Bytecode::Ret,
            ],
        )
        .build();

    // Build main module: 0x0::M with local "double" + foreign call to Dep::double
    let (builder, dep_handle) =
        CompiledModuleBuilder::new().foreign_module(AccountAddress::ZERO, "Dep");
    let module = builder
        .foreign_function(
            dep_handle,
            "double",
            vec![SignatureToken::U64],
            vec![SignatureToken::U64],
        )
        .function(
            "double",
            vec![SignatureToken::U64],
            vec![SignatureToken::U64],
            vec![],
            vec![
                Bytecode::CopyLoc(0),
                Bytecode::CopyLoc(0),
                Bytecode::Add,
                Bytecode::Ret,
            ],
        )
        .function(
            "caller",
            vec![SignatureToken::U64],
            vec![SignatureToken::U64],
            vec![],
            vec![
                Bytecode::CopyLoc(0),
                Bytecode::Call(FunctionHandleIndex(0)), // foreign Dep::double
                Bytecode::Call(FunctionHandleIndex(1)), // local double
                Bytecode::Ret,
            ],
        )
        .build();

    let asm = compiler::compile_module_with_deps(&target, &module, &[dep]).unwrap();

    assert!(
        asm.contains("_mv_0x0_M_double"),
        "missing local symbol 0x0_M_double\nassembly:\n{asm}"
    );
    assert!(
        asm.contains("_mv_0x0_Dep_double"),
        "missing external symbol 0x0_Dep_double\nassembly:\n{asm}"
    );
}

/// Serialize -> deserialize -> compile: verifies the `compile(&[u8])` entry point
/// that real callers use with `.mv` files.
#[rstest]
#[case::aarch64(Target::Aarch64)]
#[case::riscv64(Target::Riscv64)]
fn serialization_round_trip(#[case] target: Target) {
    let module = CompiledModuleBuilder::new()
        .function(
            "add",
            vec![SignatureToken::U64, SignatureToken::U64],
            vec![SignatureToken::U64],
            vec![],
            vec![
                Bytecode::CopyLoc(0),
                Bytecode::CopyLoc(1),
                Bytecode::Add,
                Bytecode::Ret,
            ],
        )
        .build();

    let mut bytecode = Vec::new();
    module
        .serialize_with_version(module.version, &mut bytecode)
        .expect("serialization failed");

    let asm = compiler::compile(&target, &bytecode).expect("compile failed");

    assert!(
        asm.contains("\tadd\t") || asm.contains("\tadds\t") || asm.contains("\taddi\t"),
        "should contain add instruction"
    );
    assert!(asm.contains("\tret"), "should contain ret instruction");
}
