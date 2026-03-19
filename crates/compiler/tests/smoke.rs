// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the Move-to-LLVM compiler.

use compiler::module::CompiledModuleBuilder;
use compiler::{Compiler, Target};
use move_binary_format::file_format::{Bytecode, FunctionHandleIndex, SignatureToken};
use move_core_types::account_address::AccountAddress;

#[test]
fn kitchen_sink_compiles() {
    let (module, deps) = CompiledModuleBuilder::kitchen_sink();
    let asm = Compiler::compile_module_with_dependencies(&Target::host(), &module, &deps).unwrap();

    // Verify all function symbols are present
    for name in &[
        // Structs
        "0x0_M_make_point",
        "0x0_M_sum_point",
        // Arithmetic & types
        "0x0_M_forty_two",
        "0x0_M_low_byte",
        "0x0_M_cast_widths",
        "0x0_M_add_u16",
        "0x0_M_add_u32",
        "0x0_M_add_u128",
        "0x0_M_add_u256",
        "0x0_M_discard",
        // References
        "0x0_M_swap_fields",
        "0x0_M_freeze_and_read",
        "0x0_M_read_x",
        // Control flow
        "0x0_M_swap_u64",
        "0x0_M_checked_sub",
        // Calls & generics
        "0x0_M_round_trip",
        "0x0_M_identity",
        "0x0_M_call_identity",
        // Loops
        "0x0_M_sum_loop",
        // Integration
        "0x0_M_integration_test",
        // Cross-module
        "0x0_M_call_double",
        // Vectors
        "0x0_M_test_vec",
        // Equality
        "0x0_M_eq_points",
        "0x0_M_eq_refs",
        "0x0_M_neq_u64",
        // Phantom generics
        "0x0_M_phantom_read_x",
        "0x0_M_phantom_proxy",
    ] {
        assert!(
            asm.contains(name),
            "assembly should contain '{name}'\nassembly:\n{asm}"
        );
    }

    // Key instruction patterns (tab-prefixed to avoid matching labels/symbols)
    assert!(asm.contains("\tbl\t"), "should contain function calls (bl)");
    assert!(
        asm.contains("\tb."),
        "should contain conditional branches (b.cond)"
    );
    assert!(
        asm.contains("\tret"),
        "should contain function returns (ret)"
    );
    assert!(
        asm.contains("0x0_M_identity$u64"),
        "should contain monomorphized generic (identity$u64)"
    );
    assert!(
        asm.contains("0x0_M_phantom_read_x$u64"),
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

    // LLVM emits underscore-prefixed symbols on macOS
    assert!(
        asm.contains("_0x0_M_make_point"),
        "should contain LLVM symbol _0x0_M_make_point\nassembly:\n{asm}"
    );

    // Cross-module call: call_double should emit a `bl` to the external `double` symbol
    assert!(
        asm.contains("bl\t_0x0_Dep_double") || asm.contains("bl _0x0_Dep_double"),
        "should contain a branch-and-link to external 'double'\nassembly:\n{asm}"
    );

    // Vector ops: runtime stubs are referenced
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
}

#[test]
fn same_name_cross_module_no_collision() {
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
    // FunctionHandleIndex(0) = foreign Dep::double
    // FunctionHandleIndex(1) = local double
    // FunctionHandleIndex(2) = local caller
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

    let asm = Compiler::compile_module_with_dependencies(&Target::host(), &module, &[dep]).unwrap();

    assert!(
        asm.contains("0x0_M_double"),
        "missing local symbol 0x0_M_double\nassembly:\n{asm}"
    );
    assert!(
        asm.contains("0x0_Dep_double"),
        "missing external symbol 0x0_Dep_double\nassembly:\n{asm}"
    );
}

/// Serialize → deserialize → compile: verifies the `compile(&[u8])` entry point
/// that real callers use with `.mv` files.
#[test]
fn serialization_round_trip() {
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

    let asm = compiler::compile(&Target::host(), &bytecode).expect("compile failed");

    assert!(
        asm.contains("\tadd\t") || asm.contains("\tadds\t"),
        "should contain add instruction"
    );
    assert!(asm.contains("\tret"), "should contain ret instruction");
}
