// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Tests for the freestanding object pipeline: emit_object, set_module_assembly, linked_text.

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
    let obj = compiler.emit_object().unwrap();

    let bytes = obj.as_bytes();
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
    let obj = compiler.emit_object().unwrap();

    use object::{Object, ObjectSymbol};
    let parsed = object::File::parse(obj.as_bytes()).unwrap();
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

#[test]
fn emit_object_linked_text_round_trip() {
    let module = load_add_module();
    let context = Context::create();
    let compiler = Compiler::new(&Target::Riscv64, &context, &module, &[]).unwrap();

    let stub = ".globl _start\n_start:\n\tcall _mv_0x0_M_add\n\tret\n\
                .globl __move_rt_arithmetic_error\n__move_rt_arithmetic_error:\n\tret\n";
    compiler.set_module_assembly(stub);

    let obj = compiler.emit_object().unwrap();
    let linked = obj.linked_text("_start").unwrap();

    assert!(!linked.code.is_empty(), "linked code should not be empty");
    assert!(
        linked.entry_offset < linked.code.len() as u64,
        "entry offset {} should be within code (len {})",
        linked.entry_offset,
        linked.code.len()
    );
}

#[test]
fn emit_object_linked_text_resolves_calls() {
    let module = load_add_module();
    let context = Context::create();
    let compiler = Compiler::new(&Target::Riscv64, &context, &module, &[]).unwrap();

    let stub = ".globl _start\n_start:\n\tcall _mv_0x0_M_add\n\tret\n\
                .globl __move_rt_arithmetic_error\n__move_rt_arithmetic_error:\n\tret\n";
    compiler.set_module_assembly(stub);

    let obj = compiler.emit_object().unwrap();
    let linked = obj.linked_text("_start").unwrap();

    // The call instruction is an auipc+jalr pair at _start (entry_offset).
    // After relocation, at least one of them should have a non-zero immediate.
    let off = linked.entry_offset as usize;
    let auipc = u32::from_le_bytes(linked.code[off..off + 4].try_into().unwrap());
    let jalr = u32::from_le_bytes(linked.code[off + 4..off + 8].try_into().unwrap());
    let hi20 = (auipc >> 12) & 0xfffff;
    let lo12 = (jalr >> 20) & 0xfff;
    assert!(
        hi20 != 0 || lo12 != 0,
        "relocation not applied: auipc={auipc:#x} jalr={jalr:#x}"
    );
}

#[test]
fn linked_text_missing_entry_is_error() {
    let module = load_add_module();
    let context = Context::create();
    let compiler = Compiler::new(&Target::Riscv64, &context, &module, &[]).unwrap();
    compiler.set_module_assembly(
        ".globl __move_rt_arithmetic_error\n__move_rt_arithmetic_error:\n\tret\n",
    );
    let obj = compiler.emit_object().unwrap();

    let err = obj.linked_text("nonexistent").unwrap_err();
    assert!(
        err.to_string().contains("not found"),
        "expected 'not found' error, got: {err}"
    );
}
