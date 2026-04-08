// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Tests for emit_object and set_module_assembly.

use compiler::{Compiler, Target};
use inkwell::context::Context;
use move_binary_format::CompiledModule;

fn load_add_module() -> CompiledModule {
    let bytecode = std::fs::read(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/move/custom/add.mv"
    ))
    .unwrap();
    CompiledModule::deserialize_with_defaults(&bytecode).unwrap()
}

#[test]
fn emit_object_produces_valid_elf() {
    let module = load_add_module();
    let context = Context::create();
    let compiler = Compiler::new(&Target::Riscv64, &context, &module, &[]).unwrap();
    let object = compiler.emit_object().unwrap();

    let bytes = object.as_bytes();
    assert!(
        bytes.len() > 100,
        "object file too small: {} bytes",
        bytes.len()
    );
    assert_eq!(&bytes[..4], b"\x7fELF", "should be valid ELF");
}

#[test]
fn set_module_assembly_injects_symbols() {
    let module = load_add_module();
    let context = Context::create();
    let compiler = Compiler::new(&Target::Riscv64, &context, &module, &[]).unwrap();
    compiler.set_module_assembly(".globl _start\n_start:\n\tret\n");
    let object = compiler.emit_object().unwrap();

    use object::{Object, ObjectSymbol};
    let parsed = object::File::parse(object.as_bytes()).unwrap();
    let symbols: Vec<String> = parsed
        .symbols()
        .filter_map(|s| s.name().ok().map(|n| n.to_string()))
        .collect();

    assert!(
        symbols.iter().any(|s| s == "_start"),
        "injected _start missing from symbols: {symbols:?}"
    );
    assert!(
        symbols.iter().any(|s| s.contains("_mv_0x0_M_add")),
        "Move function symbol missing: {symbols:?}"
    );
}
