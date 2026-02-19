// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::{path::Path, process::Command};

use move_binary_format::{CompiledModule, file_format::*};
use move_core_types::{account_address::AccountAddress, identifier::Identifier};
use tempfile::TempDir;

/// Build a single-function Move module with the given signature and bytecode body.
fn make_module(
    fn_name: &str,
    params: Vec<SignatureToken>,
    returns: Vec<SignatureToken>,
    locals: Vec<SignatureToken>,
    code: Vec<Bytecode>,
) -> CompiledModule {
    CompiledModule {
        version: 7,
        publishable: true,
        self_module_handle_idx: ModuleHandleIndex(0),
        module_handles: vec![ModuleHandle {
            address: AddressIdentifierIndex(0),
            name: IdentifierIndex(0),
        }],
        identifiers: vec![
            Identifier::new("M").unwrap(),
            Identifier::new(fn_name).unwrap(),
        ],
        address_identifiers: vec![AccountAddress::ZERO],
        function_handles: vec![FunctionHandle {
            module: ModuleHandleIndex(0),
            name: IdentifierIndex(1),
            parameters: SignatureIndex(0),
            return_: SignatureIndex(1),
            type_parameters: vec![],
        }],
        function_defs: vec![FunctionDefinition {
            function: FunctionHandleIndex(0),
            visibility: Visibility::Public,
            is_entry: false,
            acquires_global_resources: vec![],
            code: Some(CodeUnit {
                locals: SignatureIndex(2),
                code,
                jump_tables: vec![],
            }),
        }],
        signatures: vec![Signature(params), Signature(returns), Signature(locals)],
        struct_defs: vec![],
        datatype_handles: vec![],
        constant_pool: vec![],
        metadata: vec![],
        field_handles: vec![],
        friend_decls: vec![],
        struct_def_instantiations: vec![],
        function_instantiations: vec![],
        field_instantiations: vec![],
        enum_defs: vec![],
        enum_def_instantiations: vec![],
        variant_handles: vec![],
        variant_instantiation_handles: vec![],
    }
}

/// Build a minimal Move module with a single `add(u64, u64): u64` function.
fn make_add_module() -> CompiledModule {
    make_module(
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
}

/// Serialize → deserialize → compile: the true end-to-end path through `compile()`.
#[test]
fn end_to_end_from_serialized_bytecode() {
    let module = make_add_module();

    // Serialize to raw bytes (what you'd get from a .mv file)
    let mut bytecode = Vec::new();
    module
        .serialize_with_version(module.version, &mut bytecode)
        .expect("serialization failed");

    // This is the public API entry point — bytes in, assembly out
    let asm = move_to_llvm::compile(&bytecode).expect("compile from bytecode failed");

    assert!(asm.contains("add"), "assembly should contain 'add'");
    assert!(asm.contains("ret"), "assembly should contain ret");
    assert!(
        !asm.contains("x23"),
        "assembly should not reference x23 (reserved)"
    );
}

/// End-to-end from the checked-in .mv file (tests/move_samples/add.mv).
#[test]
fn end_to_end_from_mv_file() {
    let bytecode = include_bytes!("../../../tests/move_samples/add.mv");

    let asm = move_to_llvm::compile(bytecode).expect("compile from .mv file failed");

    assert!(asm.contains("add"), "assembly should contain 'add'");
    assert!(asm.contains("ret"), "assembly should contain ret");
}

#[test]
fn compile_add_produces_valid_assembly() {
    let module = make_add_module();
    let asm = move_to_llvm::compile_module(&module).expect("compilation failed");

    // Should contain a global symbol for the function
    assert!(
        asm.contains("add"),
        "assembly should contain 'add' function name"
    );
    // Should contain a ret instruction
    assert!(asm.contains("ret"), "assembly should contain ret");
    // x23 should NOT appear (LLVM reserved it)
    assert!(
        !asm.contains("x23"),
        "assembly should not reference x23 (reserved register)\nassembly:\n{asm}"
    );
}

/// Assembles the given assembly source into an object file.
fn assemble(source: &str, obj_path: &Path) {
    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let asm_path = temp_dir.path().join("test.s");
    std::fs::write(&asm_path, source).expect("failed to write asm");

    let status = Command::new("as")
        .args(["-o", obj_path.to_str().unwrap(), asm_path.to_str().unwrap()])
        .status()
        .expect("failed to run assembler");

    assert!(status.success(), "assembler failed");
}

/// Extracts the text section from an object file.
fn extract_text_section(obj_path: &Path) -> Vec<u8> {
    let data = std::fs::read(obj_path).expect("failed to read object file");
    let file = object::File::parse(&*data).expect("failed to parse object file");

    use object::{Object, ObjectSection};
    for section in file.sections() {
        let name = section.name().unwrap_or("");
        if name == "__text" || name == ".text" {
            return section
                .data()
                .expect("failed to read text section")
                .to_vec();
        }
    }
    panic!("text section not found in object file");
}

// ---------------------------------------------------------------------------
// ExecutableCode: mmap-based JIT execution for aarch64 tests
// ---------------------------------------------------------------------------

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
struct ExecutableCode {
    ptr: *mut u8,
    len: usize,
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
impl ExecutableCode {
    /// Load machine code bytes into executable memory via mmap.
    ///
    /// Uses a two-step approach (write then mprotect) to satisfy macOS W^X policy.
    fn load(code: &[u8]) -> Self {
        use libc::{
            _SC_PAGESIZE, MAP_ANON, MAP_PRIVATE, PROT_EXEC, PROT_READ, PROT_WRITE, mmap, mprotect,
            sysconf,
        };
        use std::ptr;

        let page_size = unsafe { sysconf(_SC_PAGESIZE) } as usize;
        let len = (code.len() + page_size - 1) & !(page_size - 1); // round up

        // Step 1: mmap writable (not executable)
        let ptr = unsafe {
            mmap(
                ptr::null_mut(),
                len,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANON,
                -1,
                0,
            )
        };
        assert_ne!(ptr, libc::MAP_FAILED, "mmap failed");

        // Step 2: copy code
        let ptr = ptr as *mut u8;
        unsafe { ptr::copy_nonoverlapping(code.as_ptr(), ptr, code.len()) };

        // Step 3: switch to read+execute (drop write)
        let rc = unsafe { mprotect(ptr as *mut libc::c_void, len, PROT_READ | PROT_EXEC) };
        assert_eq!(rc, 0, "mprotect failed");

        // Step 4: flush icache
        #[cfg(target_os = "macos")]
        unsafe {
            extern "C" {
                fn sys_icache_invalidate(start: *mut libc::c_void, size: usize);
            }
            sys_icache_invalidate(ptr as *mut libc::c_void, code.len());
        }
        #[cfg(target_os = "linux")]
        unsafe {
            extern "C" {
                fn __clear_cache(start: *mut libc::c_void, end: *mut libc::c_void);
            }
            __clear_cache(
                ptr as *mut libc::c_void,
                ptr.add(code.len()) as *mut libc::c_void,
            );
        }

        ExecutableCode { ptr, len }
    }

    /// Transmute the mapped memory to a function pointer.
    ///
    /// # Safety
    /// The caller must ensure `F` matches the ABI and signature of the loaded code.
    unsafe fn as_fn<F: Copy>(&self) -> F {
        assert!(
            std::mem::size_of::<F>() == std::mem::size_of::<*const ()>(),
            "F must be a function pointer"
        );
        unsafe { std::mem::transmute_copy(&self.ptr) }
    }
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
impl Drop for ExecutableCode {
    fn drop(&mut self) {
        unsafe {
            libc::munmap(self.ptr as *mut libc::c_void, self.len);
        }
    }
}

/// Compile a module, assemble it, extract machine code, and load into executable memory.
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn compile_and_load(module: &CompiledModule) -> ExecutableCode {
    let asm = move_to_llvm::compile_module(module).expect("compilation failed");
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );
    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let obj_path = temp_dir.path().join("test.o");
    assemble(&asm, &obj_path);
    let code = extract_text_section(&obj_path);
    ExecutableCode::load(&code)
}

// ---------------------------------------------------------------------------
// Compilation tests for operations (run on all platforms)
// ---------------------------------------------------------------------------

#[test]
fn compile_comparisons() {
    for (name, op) in [
        ("lt", Bytecode::Lt),
        ("gt", Bytecode::Gt),
        ("le", Bytecode::Le),
        ("ge", Bytecode::Ge),
        ("eq", Bytecode::Eq),
        ("neq", Bytecode::Neq),
    ] {
        let module = make_module(
            name,
            vec![SignatureToken::U64, SignatureToken::U64],
            vec![SignatureToken::Bool],
            vec![],
            vec![
                Bytecode::CopyLoc(0),
                Bytecode::CopyLoc(1),
                op,
                Bytecode::Ret,
            ],
        );
        move_to_llvm::compile_module(&module)
            .unwrap_or_else(|e| panic!("{name} compilation failed: {e}"));
    }
}

#[test]
fn compile_bitwise_ops() {
    for (name, op) in [
        ("bitand", Bytecode::BitAnd),
        ("bitor", Bytecode::BitOr),
        ("xor", Bytecode::Xor),
    ] {
        let module = make_module(
            name,
            vec![SignatureToken::U64, SignatureToken::U64],
            vec![SignatureToken::U64],
            vec![],
            vec![
                Bytecode::CopyLoc(0),
                Bytecode::CopyLoc(1),
                op,
                Bytecode::Ret,
            ],
        );
        move_to_llvm::compile_module(&module)
            .unwrap_or_else(|e| panic!("{name} compilation failed: {e}"));
    }
}

#[test]
fn compile_shifts() {
    for (name, op) in [("shl", Bytecode::Shl), ("shr", Bytecode::Shr)] {
        let module = make_module(
            name,
            vec![SignatureToken::U64, SignatureToken::U8],
            vec![SignatureToken::U64],
            vec![],
            vec![
                Bytecode::CopyLoc(0),
                Bytecode::CopyLoc(1),
                op,
                Bytecode::Ret,
            ],
        );
        move_to_llvm::compile_module(&module)
            .unwrap_or_else(|e| panic!("{name} compilation failed: {e}"));
    }
}

#[test]
fn compile_logical_not() {
    let module = make_module(
        "not",
        vec![SignatureToken::Bool],
        vec![SignatureToken::Bool],
        vec![],
        vec![Bytecode::CopyLoc(0), Bytecode::Not, Bytecode::Ret],
    );
    move_to_llvm::compile_module(&module).expect("not compilation failed");
}

#[test]
fn compile_logical_and_or() {
    for (name, op) in [("and", Bytecode::And), ("or", Bytecode::Or)] {
        let module = make_module(
            name,
            vec![SignatureToken::Bool, SignatureToken::Bool],
            vec![SignatureToken::Bool],
            vec![],
            vec![
                Bytecode::CopyLoc(0),
                Bytecode::CopyLoc(1),
                op,
                Bytecode::Ret,
            ],
        );
        move_to_llvm::compile_module(&module)
            .unwrap_or_else(|e| panic!("{name} compilation failed: {e}"));
    }
}

#[test]
fn compile_casts() {
    for (name, op, ret) in [
        ("cast_u8", Bytecode::CastU8, SignatureToken::U8),
        ("cast_u16", Bytecode::CastU16, SignatureToken::U16),
        ("cast_u32", Bytecode::CastU32, SignatureToken::U32),
        ("cast_u64", Bytecode::CastU64, SignatureToken::U64),
        ("cast_u128", Bytecode::CastU128, SignatureToken::U128),
        ("cast_u256", Bytecode::CastU256, SignatureToken::U256),
    ] {
        let module = make_module(
            name,
            vec![SignatureToken::U64],
            vec![ret],
            vec![],
            vec![Bytecode::CopyLoc(0), op, Bytecode::Ret],
        );
        move_to_llvm::compile_module(&module)
            .unwrap_or_else(|e| panic!("{name} compilation failed: {e}"));
    }
}

// ---------------------------------------------------------------------------
// Execution tests (aarch64 only)
// ---------------------------------------------------------------------------

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_comparisons() {
    for (name, op, cases) in [
        (
            "lt",
            Bytecode::Lt,
            vec![(3u64, 4u64, 1u8), (4, 3, 0), (4, 4, 0)],
        ),
        ("gt", Bytecode::Gt, vec![(4, 3, 1), (3, 4, 0), (4, 4, 0)]),
        ("le", Bytecode::Le, vec![(3, 4, 1), (4, 4, 1), (4, 3, 0)]),
        ("ge", Bytecode::Ge, vec![(4, 3, 1), (4, 4, 1), (3, 4, 0)]),
        ("eq", Bytecode::Eq, vec![(4, 4, 1), (3, 4, 0)]),
        ("neq", Bytecode::Neq, vec![(3, 4, 1), (4, 4, 0)]),
    ] {
        let module = make_module(
            name,
            vec![SignatureToken::U64, SignatureToken::U64],
            vec![SignatureToken::Bool],
            vec![],
            vec![
                Bytecode::CopyLoc(0),
                Bytecode::CopyLoc(1),
                op,
                Bytecode::Ret,
            ],
        );
        let exec = compile_and_load(&module);
        type CmpFn = unsafe extern "C" fn(u64, u64) -> u8;
        let f: CmpFn = unsafe { exec.as_fn() };

        for (a, b, expected) in &cases {
            let result = unsafe { f(*a, *b) };
            assert_eq!(result, *expected, "{name}({a}, {b}) should be {expected}");
        }
    }
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_bitwise_ops() {
    for (name, op, a, b, expected) in [
        ("bitand", Bytecode::BitAnd, 0xFF_u64, 0x0F, 0x0F_u64),
        ("bitor", Bytecode::BitOr, 0xF0, 0x0F, 0xFF),
        ("xor", Bytecode::Xor, 0xFF, 0x0F, 0xF0),
    ] {
        let module = make_module(
            name,
            vec![SignatureToken::U64, SignatureToken::U64],
            vec![SignatureToken::U64],
            vec![],
            vec![
                Bytecode::CopyLoc(0),
                Bytecode::CopyLoc(1),
                op,
                Bytecode::Ret,
            ],
        );
        let exec = compile_and_load(&module);
        type BinFn = unsafe extern "C" fn(u64, u64) -> u64;
        let f: BinFn = unsafe { exec.as_fn() };
        let result = unsafe { f(a, b) };
        assert_eq!(result, expected, "{name}(0x{a:X}, 0x{b:X})");
    }
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_shifts() {
    for (name, op, val, amt, expected) in [
        ("shl", Bytecode::Shl, 1_u64, 4_u8, 16_u64),
        ("shr", Bytecode::Shr, 256, 4, 16),
    ] {
        let module = make_module(
            name,
            vec![SignatureToken::U64, SignatureToken::U8],
            vec![SignatureToken::U64],
            vec![],
            vec![
                Bytecode::CopyLoc(0),
                Bytecode::CopyLoc(1),
                op,
                Bytecode::Ret,
            ],
        );
        let exec = compile_and_load(&module);
        type ShiftFn = unsafe extern "C" fn(u64, u8) -> u64;
        let f: ShiftFn = unsafe { exec.as_fn() };
        let result = unsafe { f(val, amt) };
        assert_eq!(result, expected, "{name}({val}, {amt})");
    }
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_logical_not() {
    let module = make_module(
        "not",
        vec![SignatureToken::Bool],
        vec![SignatureToken::Bool],
        vec![],
        vec![Bytecode::CopyLoc(0), Bytecode::Not, Bytecode::Ret],
    );
    let exec = compile_and_load(&module);
    type NotFn = unsafe extern "C" fn(u8) -> u8;
    let f: NotFn = unsafe { exec.as_fn() };
    assert_eq!(unsafe { f(0) }, 1, "not(false) should be true");
    assert_eq!(unsafe { f(1) }, 0, "not(true) should be false");
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_cast_truncate() {
    let module = make_module(
        "cast",
        vec![SignatureToken::U64],
        vec![SignatureToken::U8],
        vec![],
        vec![Bytecode::CopyLoc(0), Bytecode::CastU8, Bytecode::Ret],
    );
    let exec = compile_and_load(&module);
    type CastFn = unsafe extern "C" fn(u64) -> u8;
    let f: CastFn = unsafe { exec.as_fn() };
    assert_eq!(unsafe { f(258) }, 2, "cast_u8(258) should be 2");
    assert_eq!(unsafe { f(42) }, 42, "cast_u8(42) should be 42");
}

// ---------------------------------------------------------------------------
// Loop test: sum_to_n
// ---------------------------------------------------------------------------

/// Build a module with `sum_to_n(n: u64): u64` — sums 0..n in a while loop.
fn make_sum_to_n_module() -> CompiledModule {
    make_module(
        "sum_to_n",
        vec![SignatureToken::U64],                      // params: [n]
        vec![SignatureToken::U64],                      // return: [u64]
        vec![SignatureToken::U64, SignatureToken::U64], // locals: [sum, i]
        vec![
            // sum = 0, i = 0
            Bytecode::LdU64(0), // 0
            Bytecode::StLoc(1), // 1: sum = 0
            Bytecode::LdU64(0), // 2
            Bytecode::StLoc(2), // 3: i = 0
            // LOOP: while i < n
            Bytecode::CopyLoc(2),  // 4: push i
            Bytecode::CopyLoc(0),  // 5: push n
            Bytecode::Lt,          // 6: i < n
            Bytecode::BrFalse(17), // 7: if false, jump to END
            // sum += i
            Bytecode::CopyLoc(1), // 8: push sum
            Bytecode::CopyLoc(2), // 9: push i
            Bytecode::Add,        // 10: sum + i
            Bytecode::StLoc(1),   // 11: sum = sum + i
            // i += 1
            Bytecode::CopyLoc(2), // 12: push i
            Bytecode::LdU64(1),   // 13: push 1
            Bytecode::Add,        // 14: i + 1
            Bytecode::StLoc(2),   // 15: i = i + 1
            Bytecode::Branch(4),  // 16: jump to LOOP
            // END:
            Bytecode::MoveLoc(1), // 17: push sum
            Bytecode::Ret,        // 18: return
        ],
    )
}

#[test]
fn compile_sum_to_n_loop() {
    let module = make_sum_to_n_module();
    let asm = move_to_llvm::compile_module(&module).expect("sum_to_n compilation failed");

    assert!(asm.contains("ret"), "assembly should contain ret");
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_sum_to_n_loop() {
    let module = make_sum_to_n_module();
    let exec = compile_and_load(&module);

    // No gas instrumentation — the loop terminates naturally.
    type SumFn = unsafe extern "C" fn(u64) -> u64;
    let f: SumFn = unsafe { exec.as_fn() };

    assert_eq!(unsafe { f(10) }, 45, "sum_to_n(10) should be 45");
    assert_eq!(unsafe { f(0) }, 0, "sum_to_n(0) should be 0");
    assert_eq!(unsafe { f(1) }, 0, "sum_to_n(1) should be 0");
    assert_eq!(unsafe { f(100) }, 4950, "sum_to_n(100) should be 4950");
}
