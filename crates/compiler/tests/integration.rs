// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the Move-to-LLVM compiler.

use compiler::module::CompiledModuleBuilder;
use compiler::{Compiler, Target};
use move_binary_format::file_format::{Bytecode, SignatureToken};

#[test]
fn all_features_compiles() {
    let (module, deps) = CompiledModuleBuilder::all_features();
    let asm = Compiler::compile_module_with_dependencies(&Target::host(), &module, &deps).unwrap();

    // Verify all function symbols are present
    for name in &[
        "make_point",
        "sum_point",
        "round_trip",
        "identity",
        "call_identity",
        "sum_loop",
        "swap_fields",
        "swap_u64",
        "checked_sub",
        "low_byte",
        "forty_two",
        "integration_test",
        "call_double",
        "test_vec",
        "cast_widths",
        "freeze_and_read",
        "discard",
        "read_x",
        "add_u16",
        "add_u32",
        "add_u128",
        "add_u256",
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
        asm.contains("identity$u64"),
        "should contain monomorphized generic (identity$u64)"
    );
    assert!(
        asm.contains("__move_rt_abort"),
        "should contain abort runtime call"
    );

    // Symbol aliases: LLVM emits underscore-prefixed, alias adds bare name
    assert!(
        asm.contains("_make_point"),
        "should contain LLVM symbol _make_point\nassembly:\n{asm}"
    );
    assert!(
        asm.contains("\nmake_point:"),
        "should contain alias label make_point:\nassembly:\n{asm}"
    );

    // Cross-module call: call_double should emit a `bl` to the external `double` symbol
    assert!(
        asm.contains("bl\t_double") || asm.contains("bl _double"),
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

    assert!(asm.contains("\tadd\t"), "should contain add instruction");
    assert!(asm.contains("\tret"), "should contain ret instruction");
}
