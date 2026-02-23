// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::{path::Path, process::Command};

use move_binary_format::{CompiledModule, file_format::*};
use move_core_types::{account_address::AccountAddress, identifier::Identifier};
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
use std::ffi::CString;
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

// ---------------------------------------------------------------------------
// Function call tests
// ---------------------------------------------------------------------------

/// Build a module with two functions:
///   - `double(x: u64): u64 { x + x }`
///   - `quadruple(x: u64): u64 { double(double(x)) }`
fn make_caller_callee_module() -> CompiledModule {
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
            Identifier::new("double").unwrap(),
            Identifier::new("quadruple").unwrap(),
        ],
        address_identifiers: vec![AccountAddress::ZERO],
        function_handles: vec![
            // FunctionHandleIndex(0) → double
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(1),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(1),
                type_parameters: vec![],
            },
            // FunctionHandleIndex(1) → quadruple
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(2),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(1),
                type_parameters: vec![],
            },
        ],
        function_defs: vec![
            // double(x: u64): u64 { x + x }
            FunctionDefinition {
                function: FunctionHandleIndex(0),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: Some(CodeUnit {
                    locals: SignatureIndex(2),
                    code: vec![
                        Bytecode::CopyLoc(0),
                        Bytecode::CopyLoc(0),
                        Bytecode::Add,
                        Bytecode::Ret,
                    ],
                    jump_tables: vec![],
                }),
            },
            // quadruple(x: u64): u64 { double(double(x)) }
            // temps: [x, inner, result]
            FunctionDefinition {
                function: FunctionHandleIndex(1),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: Some(CodeUnit {
                    locals: SignatureIndex(3),
                    code: vec![
                        Bytecode::CopyLoc(0),                   // push x
                        Bytecode::Call(FunctionHandleIndex(0)), // inner = double(x)
                        Bytecode::StLoc(1),                     // store inner
                        Bytecode::CopyLoc(1),                   // push inner
                        Bytecode::Call(FunctionHandleIndex(0)), // result = double(inner)
                        Bytecode::StLoc(2),                     // store result
                        Bytecode::MoveLoc(2),                   // push result
                        Bytecode::Ret,
                    ],
                    jump_tables: vec![],
                }),
            },
        ],
        signatures: vec![
            Signature(vec![SignatureToken::U64]), // 0: params (x: u64)
            Signature(vec![SignatureToken::U64]), // 1: return (u64)
            Signature(vec![]),                    // 2: locals for double
            Signature(vec![SignatureToken::U64, SignatureToken::U64]), // 3: locals for quadruple
        ],
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

#[test]
fn compile_function_call() {
    let module = make_caller_callee_module();
    let asm = move_to_llvm::compile_module(&module).expect("function call compilation failed");

    assert!(
        asm.contains("double"),
        "assembly should contain 'double' symbol\nassembly:\n{asm}"
    );
    assert!(
        asm.contains("quadruple"),
        "assembly should contain 'quadruple' symbol\nassembly:\n{asm}"
    );
    assert!(
        asm.contains("bl"),
        "assembly should contain a 'bl' (call) instruction\nassembly:\n{asm}"
    );
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );
}

/// Find the byte offset of a symbol within the text section of an object file.
fn find_symbol_offset(obj_path: &Path, name: &str) -> u64 {
    use object::{Object, ObjectSection, ObjectSymbol};

    let data = std::fs::read(obj_path).expect("failed to read object file");
    let file = object::File::parse(&*data).expect("failed to parse object file");

    // On macOS, symbols have a leading underscore.
    let candidates: Vec<String> = vec![name.to_string(), format!("_{name}")];

    for sym in file.symbols() {
        let sym_name = sym.name().unwrap_or("");
        if candidates.iter().any(|c| c == sym_name) {
            // Get the symbol's address relative to the text section.
            let section_idx = sym.section_index().expect("symbol has no section");
            let section = file
                .section_by_index(section_idx)
                .expect("bad section index");
            return sym.address() - section.address();
        }
    }
    panic!("symbol '{name}' not found in object file");
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
impl ExecutableCode {
    /// Get a function pointer at a given byte offset into the loaded code.
    ///
    /// # Safety
    /// The caller must ensure `F` matches the ABI and signature of the code at `offset`.
    unsafe fn as_fn_at<F: Copy>(&self, offset: usize) -> F {
        assert!(
            std::mem::size_of::<F>() == std::mem::size_of::<*const ()>(),
            "F must be a function pointer"
        );
        let ptr = self.ptr.add(offset);
        unsafe { std::mem::transmute_copy(&ptr) }
    }
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_function_call() {
    let module = make_caller_callee_module();
    let asm = move_to_llvm::compile_module(&module).expect("compilation failed");
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );

    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let obj_path = temp_dir.path().join("test.o");
    assemble(&asm, &obj_path);

    let quadruple_offset = find_symbol_offset(&obj_path, "quadruple");

    let code = extract_text_section(&obj_path);
    let exec = ExecutableCode::load(&code);

    type QuadFn = unsafe extern "C" fn(u64) -> u64;
    let f: QuadFn = unsafe { exec.as_fn_at(quadruple_offset as usize) };

    assert_eq!(unsafe { f(5) }, 20, "quadruple(5) should be 20");
    assert_eq!(unsafe { f(0) }, 0, "quadruple(0) should be 0");
    assert_eq!(unsafe { f(100) }, 400, "quadruple(100) should be 400");
}

// ---------------------------------------------------------------------------
// Struct tests
// ---------------------------------------------------------------------------

/// Build a module with:
///   - `struct Point { x: u64, y: u64 }`
///   - `new_point(x: u64, y: u64): Point` — uses Pack
///   - `sum_point(p: Point): u64` — uses Unpack + Add
///   - `test_struct(a: u64, b: u64): u64` — chains new_point → sum_point
fn make_struct_module() -> CompiledModule {
    use move_binary_format::file_format::{
        AbilitySet, DatatypeHandle, DatatypeHandleIndex, FieldDefinition, StructDefinition,
        StructDefinitionIndex, StructFieldInformation, TypeSignature,
    };

    // Identifiers: 0=M, 1=Point, 2=new_point, 3=sum_point, 4=test_struct, 5=x, 6=y
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
            Identifier::new("Point").unwrap(),
            Identifier::new("new_point").unwrap(),
            Identifier::new("sum_point").unwrap(),
            Identifier::new("test_struct").unwrap(),
            Identifier::new("x").unwrap(),
            Identifier::new("y").unwrap(),
        ],
        address_identifiers: vec![AccountAddress::ZERO],
        datatype_handles: vec![DatatypeHandle {
            module: ModuleHandleIndex(0),
            name: IdentifierIndex(1),
            abilities: AbilitySet::PRIMITIVES,
            type_parameters: vec![],
        }],
        struct_defs: vec![StructDefinition {
            struct_handle: DatatypeHandleIndex(0),
            field_information: StructFieldInformation::Declared(vec![
                FieldDefinition {
                    name: IdentifierIndex(5),
                    signature: TypeSignature(SignatureToken::U64),
                },
                FieldDefinition {
                    name: IdentifierIndex(6),
                    signature: TypeSignature(SignatureToken::U64),
                },
            ]),
        }],
        function_handles: vec![
            // 0: new_point(u64, u64): Point
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(2),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(1),
                type_parameters: vec![],
            },
            // 1: sum_point(Point): u64
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(3),
                parameters: SignatureIndex(1),
                return_: SignatureIndex(2),
                type_parameters: vec![],
            },
            // 2: test_struct(u64, u64): u64
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(4),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(2),
                type_parameters: vec![],
            },
        ],
        function_defs: vec![
            // new_point(x: u64, y: u64): Point { Point { x, y } }
            // temps: [x, y]
            FunctionDefinition {
                function: FunctionHandleIndex(0),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: Some(CodeUnit {
                    locals: SignatureIndex(3), // empty
                    code: vec![
                        Bytecode::CopyLoc(0), // push x
                        Bytecode::CopyLoc(1), // push y
                        Bytecode::Pack(StructDefinitionIndex(0)),
                        Bytecode::Ret,
                    ],
                    jump_tables: vec![],
                }),
            },
            // sum_point(p: Point): u64 { let (x, y) = unpack(p); x + y }
            // temps: [p, x, y]
            FunctionDefinition {
                function: FunctionHandleIndex(1),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: Some(CodeUnit {
                    locals: SignatureIndex(4), // [u64, u64]
                    code: vec![
                        Bytecode::MoveLoc(0), // push p
                        Bytecode::Unpack(StructDefinitionIndex(0)),
                        Bytecode::StLoc(2),   // y
                        Bytecode::StLoc(1),   // x
                        Bytecode::CopyLoc(1), // push x
                        Bytecode::CopyLoc(2), // push y
                        Bytecode::Add,
                        Bytecode::Ret,
                    ],
                    jump_tables: vec![],
                }),
            },
            // test_struct(a: u64, b: u64): u64 { sum_point(new_point(a, b)) }
            // temps: [a, b, point, result]
            FunctionDefinition {
                function: FunctionHandleIndex(2),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: Some(CodeUnit {
                    locals: SignatureIndex(5), // [Point, u64]
                    code: vec![
                        Bytecode::CopyLoc(0),                   // push a
                        Bytecode::CopyLoc(1),                   // push b
                        Bytecode::Call(FunctionHandleIndex(0)), // new_point(a, b)
                        Bytecode::StLoc(2),                     // store point
                        Bytecode::CopyLoc(2),                   // push point
                        Bytecode::Call(FunctionHandleIndex(1)), // sum_point(point)
                        Bytecode::StLoc(3),                     // store result
                        Bytecode::MoveLoc(3),                   // push result
                        Bytecode::Ret,
                    ],
                    jump_tables: vec![],
                }),
            },
        ],
        signatures: vec![
            Signature(vec![SignatureToken::U64, SignatureToken::U64]), // 0: (u64, u64)
            Signature(vec![SignatureToken::Datatype(DatatypeHandleIndex(0))]), // 1: (Point)
            Signature(vec![SignatureToken::U64]),                      // 2: (u64)
            Signature(vec![]), // 3: empty (new_point locals)
            Signature(vec![SignatureToken::U64, SignatureToken::U64]), // 4: sum_point locals [x, y]
            Signature(vec![
                // 5: test_struct locals [Point, u64]
                SignatureToken::Datatype(DatatypeHandleIndex(0)),
                SignatureToken::U64,
            ]),
        ],
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

#[test]
fn compile_struct_pack_unpack() {
    let module = make_struct_module();
    let asm = move_to_llvm::compile_module(&module).expect("struct compilation failed");

    assert!(
        asm.contains("new_point"),
        "assembly should contain 'new_point'\nassembly:\n{asm}"
    );
    assert!(
        asm.contains("sum_point"),
        "assembly should contain 'sum_point'\nassembly:\n{asm}"
    );
    assert!(
        asm.contains("test_struct"),
        "assembly should contain 'test_struct'\nassembly:\n{asm}"
    );
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_struct_round_trip() {
    let module = make_struct_module();
    let asm = move_to_llvm::compile_module(&module).expect("compilation failed");
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );

    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let obj_path = temp_dir.path().join("test.o");
    assemble(&asm, &obj_path);

    let test_struct_offset = find_symbol_offset(&obj_path, "test_struct");

    let code = extract_text_section(&obj_path);
    let exec = ExecutableCode::load(&code);

    type TestFn = unsafe extern "C" fn(u64, u64) -> u64;
    let f: TestFn = unsafe { exec.as_fn_at(test_struct_offset as usize) };

    assert_eq!(unsafe { f(3, 7) }, 10, "test_struct(3, 7) should be 10");
    assert_eq!(unsafe { f(0, 0) }, 0, "test_struct(0, 0) should be 0");
    assert_eq!(
        unsafe { f(100, 200) },
        300,
        "test_struct(100, 200) should be 300"
    );
}

// ---------------------------------------------------------------------------
// Reference tests
// ---------------------------------------------------------------------------

/// Build a module with:
///   - `struct Pair { a: u64, b: u64 }`
///   - `swap_and_sum(p: &mut Pair): u64` — borrows fields, reads, swaps via WriteRef, returns sum
///   - `test_refs(x: u64, y: u64): u64` — packs Pair, BorrowLoc, calls swap_and_sum
fn make_ref_module() -> CompiledModule {
    use move_binary_format::file_format::{
        AbilitySet, DatatypeHandle, DatatypeHandleIndex, FieldDefinition, FieldHandle,
        FieldHandleIndex, StructDefinition, StructDefinitionIndex, StructFieldInformation,
        TypeSignature,
    };

    let pair_token = SignatureToken::Datatype(DatatypeHandleIndex(0));
    let mut_pair_ref = SignatureToken::MutableReference(Box::new(pair_token.clone()));
    let mut_u64_ref = SignatureToken::MutableReference(Box::new(SignatureToken::U64));

    // Identifiers: 0=M, 1=Pair, 2=swap_and_sum, 3=test_refs, 4=a, 5=b
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
            Identifier::new("Pair").unwrap(),
            Identifier::new("swap_and_sum").unwrap(),
            Identifier::new("test_refs").unwrap(),
            Identifier::new("a").unwrap(),
            Identifier::new("b").unwrap(),
        ],
        address_identifiers: vec![AccountAddress::ZERO],
        datatype_handles: vec![DatatypeHandle {
            module: ModuleHandleIndex(0),
            name: IdentifierIndex(1),
            abilities: AbilitySet::PRIMITIVES,
            type_parameters: vec![],
        }],
        struct_defs: vec![StructDefinition {
            struct_handle: DatatypeHandleIndex(0),
            field_information: StructFieldInformation::Declared(vec![
                FieldDefinition {
                    name: IdentifierIndex(4), // a
                    signature: TypeSignature(SignatureToken::U64),
                },
                FieldDefinition {
                    name: IdentifierIndex(5), // b
                    signature: TypeSignature(SignatureToken::U64),
                },
            ]),
        }],
        field_handles: vec![
            // FieldHandleIndex(0) → Pair.a (field 0)
            FieldHandle {
                owner: StructDefinitionIndex(0),
                field: 0,
            },
            // FieldHandleIndex(1) → Pair.b (field 1)
            FieldHandle {
                owner: StructDefinitionIndex(0),
                field: 1,
            },
        ],
        function_handles: vec![
            // 0: swap_and_sum(&mut Pair): u64
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(2),
                parameters: SignatureIndex(0), // (&mut Pair)
                return_: SignatureIndex(1),    // (u64)
                type_parameters: vec![],
            },
            // 1: test_refs(u64, u64): u64
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(3),
                parameters: SignatureIndex(2), // (u64, u64)
                return_: SignatureIndex(1),    // (u64)
                type_parameters: vec![],
            },
        ],
        function_defs: vec![
            // swap_and_sum(p: &mut Pair): u64
            // params: [p: &mut Pair]
            // locals: [ref_a: &mut u64, ref_b: &mut u64, a: u64, b: u64, sum: u64]
            FunctionDefinition {
                function: FunctionHandleIndex(0),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: Some(CodeUnit {
                    locals: SignatureIndex(3), // [&mut u64, &mut u64, u64, u64, u64]
                    code: vec![
                        // ref_a = &mut p.a
                        Bytecode::CopyLoc(0),                          // push p
                        Bytecode::MutBorrowField(FieldHandleIndex(0)), // &mut p.a
                        Bytecode::StLoc(1),                            // ref_a = ...
                        // ref_b = &mut p.b
                        Bytecode::CopyLoc(0),                          // push p
                        Bytecode::MutBorrowField(FieldHandleIndex(1)), // &mut p.b
                        Bytecode::StLoc(2),                            // ref_b = ...
                        // a = *ref_a
                        Bytecode::CopyLoc(1), // push ref_a
                        Bytecode::ReadRef,    // *ref_a
                        Bytecode::StLoc(3),   // a = ...
                        // b = *ref_b
                        Bytecode::CopyLoc(2), // push ref_b
                        Bytecode::ReadRef,    // *ref_b
                        Bytecode::StLoc(4),   // b = ...
                        // *ref_a = b  (WriteRef pops ref from top, value from below)
                        Bytecode::CopyLoc(4), // push b (value)
                        Bytecode::MoveLoc(1), // push ref_a (ref)
                        Bytecode::WriteRef,   // *ref_a = b
                        // *ref_b = a
                        Bytecode::CopyLoc(3), // push a (value)
                        Bytecode::MoveLoc(2), // push ref_b (ref)
                        Bytecode::WriteRef,   // *ref_b = a
                        // return a + b
                        Bytecode::CopyLoc(3), // push a
                        Bytecode::CopyLoc(4), // push b
                        Bytecode::Add,        // a + b
                        Bytecode::Ret,
                    ],
                    jump_tables: vec![],
                }),
            },
            // test_refs(x: u64, y: u64): u64
            // params: [x: u64, y: u64]
            // locals: [pair: Pair, ref_pair: &mut Pair, result: u64]
            FunctionDefinition {
                function: FunctionHandleIndex(1),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: Some(CodeUnit {
                    locals: SignatureIndex(4), // [Pair, &mut Pair, u64]
                    code: vec![
                        // pair = Pair { x, y }
                        Bytecode::CopyLoc(0),                     // push x
                        Bytecode::CopyLoc(1),                     // push y
                        Bytecode::Pack(StructDefinitionIndex(0)), // pack Pair
                        Bytecode::StLoc(2),                       // pair = ...
                        // ref_pair = &mut pair
                        Bytecode::MutBorrowLoc(2), // &mut pair
                        Bytecode::StLoc(3),        // ref_pair = ...
                        // result = swap_and_sum(ref_pair)
                        Bytecode::CopyLoc(3),                   // push ref_pair
                        Bytecode::Call(FunctionHandleIndex(0)), // swap_and_sum(...)
                        Bytecode::StLoc(4),                     // result = ...
                        // return result
                        Bytecode::MoveLoc(4), // push result
                        Bytecode::Ret,
                    ],
                    jump_tables: vec![],
                }),
            },
        ],
        signatures: vec![
            // 0: params for swap_and_sum: (&mut Pair)
            Signature(vec![mut_pair_ref]),
            // 1: return type: (u64)
            Signature(vec![SignatureToken::U64]),
            // 2: params for test_refs: (u64, u64)
            Signature(vec![SignatureToken::U64, SignatureToken::U64]),
            // 3: locals for swap_and_sum: [&mut u64, &mut u64, u64, u64, u64]
            Signature(vec![
                mut_u64_ref.clone(),
                mut_u64_ref,
                SignatureToken::U64,
                SignatureToken::U64,
                SignatureToken::U64,
            ]),
            // 4: locals for test_refs: [Pair, &mut Pair, u64]
            Signature(vec![
                pair_token,
                SignatureToken::MutableReference(Box::new(SignatureToken::Datatype(
                    DatatypeHandleIndex(0),
                ))),
                SignatureToken::U64,
            ]),
        ],
        constant_pool: vec![],
        metadata: vec![],
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

#[test]
fn compile_ref_ops() {
    let module = make_ref_module();
    let asm = move_to_llvm::compile_module(&module).expect("ref compilation failed");

    assert!(
        asm.contains("swap_and_sum"),
        "assembly should contain 'swap_and_sum'\nassembly:\n{asm}"
    );
    assert!(
        asm.contains("test_refs"),
        "assembly should contain 'test_refs'\nassembly:\n{asm}"
    );
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_ref_round_trip() {
    let module = make_ref_module();
    let asm = move_to_llvm::compile_module(&module).expect("compilation failed");
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );

    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let obj_path = temp_dir.path().join("test.o");
    assemble(&asm, &obj_path);

    let test_refs_offset = find_symbol_offset(&obj_path, "test_refs");

    let code = extract_text_section(&obj_path);
    let exec = ExecutableCode::load(&code);

    type TestFn = unsafe extern "C" fn(u64, u64) -> u64;
    let f: TestFn = unsafe { exec.as_fn_at(test_refs_offset as usize) };

    // swap_and_sum swaps a,b and returns a+b — sum is invariant under swap
    assert_eq!(unsafe { f(3, 7) }, 10, "test_refs(3, 7) should be 10");
    assert_eq!(unsafe { f(0, 0) }, 0, "test_refs(0, 0) should be 0");
    assert_eq!(
        unsafe { f(100, 200) },
        300,
        "test_refs(100, 200) should be 300"
    );
}

// ---------------------------------------------------------------------------
// Vector / native function tests
// ---------------------------------------------------------------------------

/// Build a `0x1::vector` module stub with all native function declarations.
fn make_vector_module_stub() -> CompiledModule {
    let type_param = AbilitySet::EMPTY;

    let t = SignatureToken::TypeParameter(0);
    let vec_t = SignatureToken::Vector(Box::new(t.clone()));
    let ref_vec_t = SignatureToken::Reference(Box::new(vec_t.clone()));
    let mut_ref_vec_t = SignatureToken::MutableReference(Box::new(vec_t.clone()));
    let ref_t = SignatureToken::Reference(Box::new(t.clone()));
    let mut_ref_t = SignatureToken::MutableReference(Box::new(t.clone()));

    CompiledModule {
        version: 7,
        publishable: true,
        self_module_handle_idx: ModuleHandleIndex(0),
        module_handles: vec![ModuleHandle {
            address: AddressIdentifierIndex(0),
            name: IdentifierIndex(0),
        }],
        identifiers: vec![
            Identifier::new("vector").unwrap(),        // 0
            Identifier::new("empty").unwrap(),         // 1
            Identifier::new("length").unwrap(),        // 2
            Identifier::new("push_back").unwrap(),     // 3
            Identifier::new("pop_back").unwrap(),      // 4
            Identifier::new("borrow").unwrap(),        // 5
            Identifier::new("borrow_mut").unwrap(),    // 6
            Identifier::new("swap").unwrap(),          // 7
            Identifier::new("destroy_empty").unwrap(), // 8
        ],
        address_identifiers: vec![AccountAddress::ONE],
        signatures: vec![
            Signature(vec![]),                                 // 0: ()
            Signature(vec![vec_t.clone()]),                    // 1: (vector<T>)
            Signature(vec![mut_ref_vec_t.clone(), t.clone()]), // 2: (&mut vec<T>, T)
            Signature(vec![t.clone()]),                        // 3: (T)
            Signature(vec![ref_vec_t]),                        // 4: (&vector<T>)
            Signature(vec![SignatureToken::U64]),              // 5: (u64)
            Signature(vec![mut_ref_vec_t.clone()]),            // 6: (&mut vec<T>)
            Signature(vec![
                SignatureToken::Reference(Box::new(vec_t.clone())),
                SignatureToken::U64,
            ]), // 7: (&vec<T>, u64)
            Signature(vec![ref_t]),                            // 8: (&T)
            Signature(vec![mut_ref_vec_t.clone(), SignatureToken::U64]), // 9: (&mut vec<T>, u64)
            Signature(vec![mut_ref_t]),                        // 10: (&mut T)
            Signature(vec![
                mut_ref_vec_t,
                SignatureToken::U64,
                SignatureToken::U64,
            ]), // 11: (&mut vec<T>, u64, u64)
        ],
        function_handles: vec![
            // 0: empty<T>(): vector<T>
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(1),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(1),
                type_parameters: vec![type_param],
            },
            // 1: length<T>(&vector<T>): u64
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(2),
                parameters: SignatureIndex(4),
                return_: SignatureIndex(5),
                type_parameters: vec![type_param],
            },
            // 2: push_back<T>(&mut vector<T>, T): void
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(3),
                parameters: SignatureIndex(2),
                return_: SignatureIndex(0),
                type_parameters: vec![type_param],
            },
            // 3: pop_back<T>(&mut vector<T>): T
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(4),
                parameters: SignatureIndex(6),
                return_: SignatureIndex(3),
                type_parameters: vec![type_param],
            },
            // 4: borrow<T>(&vector<T>, u64): &T
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(5),
                parameters: SignatureIndex(7),
                return_: SignatureIndex(8),
                type_parameters: vec![type_param],
            },
            // 5: borrow_mut<T>(&mut vector<T>, u64): &mut T
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(6),
                parameters: SignatureIndex(9),
                return_: SignatureIndex(10),
                type_parameters: vec![type_param],
            },
            // 6: swap<T>(&mut vector<T>, u64, u64): void
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(7),
                parameters: SignatureIndex(11),
                return_: SignatureIndex(0),
                type_parameters: vec![type_param],
            },
            // 7: destroy_empty<T>(vector<T>): void
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(8),
                parameters: SignatureIndex(1),
                return_: SignatureIndex(0),
                type_parameters: vec![type_param],
            },
        ],
        function_defs: vec![
            FunctionDefinition {
                function: FunctionHandleIndex(0),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: None,
            },
            FunctionDefinition {
                function: FunctionHandleIndex(1),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: None,
            },
            FunctionDefinition {
                function: FunctionHandleIndex(2),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: None,
            },
            FunctionDefinition {
                function: FunctionHandleIndex(3),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: None,
            },
            FunctionDefinition {
                function: FunctionHandleIndex(4),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: None,
            },
            FunctionDefinition {
                function: FunctionHandleIndex(5),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: None,
            },
            FunctionDefinition {
                function: FunctionHandleIndex(6),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: None,
            },
            FunctionDefinition {
                function: FunctionHandleIndex(7),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: None,
            },
        ],
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

/// Build a test module: `test_vec(a: u64, b: u64): u64`
///
/// Creates empty vector, pushes a and b, pops both, destroys empty, returns a + b.
fn make_vec_test_module() -> CompiledModule {
    // SignatureIndex(3) points to the element type [U64] for VecXxx bytecodes
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
            Identifier::new("test_vec").unwrap(),
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
                code: vec![
                    // v = empty vector<u64>
                    Bytecode::VecPack(SignatureIndex(3), 0),
                    Bytecode::StLoc(2),
                    // push_back(&mut v, a)
                    Bytecode::MutBorrowLoc(2),
                    Bytecode::CopyLoc(0),
                    Bytecode::VecPushBack(SignatureIndex(3)),
                    // push_back(&mut v, b)
                    Bytecode::MutBorrowLoc(2),
                    Bytecode::CopyLoc(1),
                    Bytecode::VecPushBack(SignatureIndex(3)),
                    // y = pop_back(&mut v)  (pops b)
                    Bytecode::MutBorrowLoc(2),
                    Bytecode::VecPopBack(SignatureIndex(3)),
                    Bytecode::StLoc(3),
                    // x = pop_back(&mut v)  (pops a)
                    Bytecode::MutBorrowLoc(2),
                    Bytecode::VecPopBack(SignatureIndex(3)),
                    Bytecode::StLoc(4),
                    // destroy_empty(v)
                    Bytecode::MoveLoc(2),
                    Bytecode::VecUnpack(SignatureIndex(3), 0),
                    // return x + y
                    Bytecode::CopyLoc(4),
                    Bytecode::CopyLoc(3),
                    Bytecode::Add,
                    Bytecode::Ret,
                ],
                jump_tables: vec![],
            }),
        }],
        signatures: vec![
            Signature(vec![SignatureToken::U64, SignatureToken::U64]), // 0: params
            Signature(vec![SignatureToken::U64]),                      // 1: return
            Signature(vec![
                // 2: locals
                SignatureToken::Vector(Box::new(SignatureToken::U64)),
                SignatureToken::U64,
                SignatureToken::U64,
            ]),
            Signature(vec![SignatureToken::U64]), // 3: element type for VecXxx
        ],
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

#[test]
fn compile_vec_ops() {
    let vec_stub = make_vector_module_stub();
    let test_module = make_vec_test_module();
    let asm = move_to_llvm::compile_module_with_deps(&test_module, &[vec_stub])
        .expect("vec ops compilation failed");

    assert!(
        asm.contains("__move_rt_0x1_vector_empty"),
        "should call vector_empty\nassembly:\n{asm}"
    );
    assert!(
        asm.contains("__move_rt_0x1_vector_push_back"),
        "should call vector_push_back\nassembly:\n{asm}"
    );
    assert!(
        asm.contains("__move_rt_0x1_vector_pop_back"),
        "should call vector_pop_back\nassembly:\n{asm}"
    );
    assert!(
        asm.contains("__move_rt_0x1_vector_destroy_empty"),
        "should call vector_destroy_empty\nassembly:\n{asm}"
    );
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );
}

/// Minimal C runtime implementing `0x1::vector` operations for u64.
///
/// Move's `&mut vector<T>` is a mutable reference: a pointer to the slot
/// holding the vector pointer (ptr-to-ptr). So `push_back` and `pop_back`
/// dereference `*vpp` to get the actual vector pointer. `empty` returns
/// the vector pointer directly and `destroy_empty` takes it by value.
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
const VEC_RUNTIME_C: &str = r#"
#include <stdlib.h>
#include <stdint.h>

typedef struct { uint64_t len; uint64_t cap; uint64_t* data; } Vec_u64;

/* empty<u64>(): vector<u64>  — returns ptr by value */
void* __move_rt_0x1_vector_empty$u64(void) {
    Vec_u64* v = (Vec_u64*)malloc(sizeof(Vec_u64));
    v->len = 0;
    v->cap = 4;
    v->data = (uint64_t*)malloc(4 * sizeof(uint64_t));
    return v;
}

/* push_back<u64>(&mut vector<u64>, u64)  — first arg is ptr-to-ptr */
void __move_rt_0x1_vector_push_back$u64(void** vpp, uint64_t val) {
    Vec_u64* v = (Vec_u64*)*vpp;
    if (v->len >= v->cap) {
        v->cap *= 2;
        v->data = (uint64_t*)realloc(v->data, v->cap * sizeof(uint64_t));
    }
    v->data[v->len++] = val;
}

/* pop_back<u64>(&mut vector<u64>): u64  — first arg is ptr-to-ptr */
uint64_t __move_rt_0x1_vector_pop_back$u64(void** vpp) {
    Vec_u64* v = (Vec_u64*)*vpp;
    return v->data[--v->len];
}

/* destroy_empty<u64>(vector<u64>)  — takes ptr by value */
void __move_rt_0x1_vector_destroy_empty$u64(void* vp) {
    Vec_u64* v = (Vec_u64*)vp;
    free(v->data);
    free(v);
}
"#;

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_vec_round_trip() {
    let vec_stub = make_vector_module_stub();
    let test_module = make_vec_test_module();
    let asm = move_to_llvm::compile_module_with_deps(&test_module, &[vec_stub])
        .expect("vec ops compilation failed");
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );

    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let asm_path = temp_dir.path().join("move.s");
    let runtime_path = temp_dir.path().join("runtime.c");
    let dylib_ext = if cfg!(target_os = "macos") {
        "dylib"
    } else {
        "so"
    };
    let dylib_path = temp_dir.path().join(format!("test.{dylib_ext}"));

    std::fs::write(&asm_path, &asm).expect("failed to write asm");
    std::fs::write(&runtime_path, VEC_RUNTIME_C).expect("failed to write runtime");

    let output = Command::new("cc")
        .args([
            "-shared",
            "-o",
            dylib_path.to_str().unwrap(),
            asm_path.to_str().unwrap(),
            runtime_path.to_str().unwrap(),
        ])
        .output()
        .expect("failed to run cc");
    assert!(
        output.status.success(),
        "cc failed to build shared library:\nstderr: {}",
        String::from_utf8_lossy(&output.stderr),
    );

    unsafe {
        let lib_path = CString::new(dylib_path.to_str().unwrap()).unwrap();
        let lib = libc::dlopen(lib_path.as_ptr(), libc::RTLD_NOW);
        if lib.is_null() {
            let err = std::ffi::CStr::from_ptr(libc::dlerror())
                .to_str()
                .unwrap_or("unknown error");
            panic!("dlopen failed: {err}");
        }

        let sym_name = CString::new("test_vec").unwrap();
        let sym = libc::dlsym(lib, sym_name.as_ptr());
        if sym.is_null() {
            let err = std::ffi::CStr::from_ptr(libc::dlerror())
                .to_str()
                .unwrap_or("unknown error");
            libc::dlclose(lib);
            panic!("dlsym failed: {err}");
        }

        let f: unsafe extern "C" fn(u64, u64) -> u64 = std::mem::transmute(sym);

        assert_eq!(f(3, 7), 10, "test_vec(3, 7) should be 10");
        assert_eq!(f(0, 0), 0, "test_vec(0, 0) should be 0");
        assert_eq!(f(100, 200), 300, "test_vec(100, 200) should be 300");

        libc::dlclose(lib);
    }
}

// ---------------------------------------------------------------------------
// Cross-module function call tests
// ---------------------------------------------------------------------------

/// Build two modules for cross-module call testing:
///   - `0x0::Dep`  with `double(x: u64): u64 { x + x }`
///   - `0x0::Main` with `call_double(x: u64): u64 { Dep::double(x) }`
fn make_cross_module_pair() -> (CompiledModule, CompiledModule) {
    // --- Dep module: double(x: u64): u64 ---
    let dep = make_module(
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
    );

    // --- Main module: call_double(x: u64): u64 ---
    // Must reference Dep's module handle and double's function handle.
    let main = CompiledModule {
        version: 7,
        publishable: true,
        self_module_handle_idx: ModuleHandleIndex(0),
        module_handles: vec![
            // 0: self (Main)
            ModuleHandle {
                address: AddressIdentifierIndex(0),
                name: IdentifierIndex(0),
            },
            // 1: Dep
            ModuleHandle {
                address: AddressIdentifierIndex(0),
                name: IdentifierIndex(1),
            },
        ],
        identifiers: vec![
            Identifier::new("Main").unwrap(),        // 0
            Identifier::new("M").unwrap(),           // 1  (Dep's module name from make_module)
            Identifier::new("call_double").unwrap(), // 2
            Identifier::new("double").unwrap(),      // 3
        ],
        address_identifiers: vec![AccountAddress::ZERO],
        function_handles: vec![
            // 0: call_double (self)
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(2),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(0),
                type_parameters: vec![],
            },
            // 1: double (from Dep)
            FunctionHandle {
                module: ModuleHandleIndex(1),
                name: IdentifierIndex(3),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(0),
                type_parameters: vec![],
            },
        ],
        function_defs: vec![
            // call_double(x: u64): u64 { Dep::double(x) }
            FunctionDefinition {
                function: FunctionHandleIndex(0),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: Some(CodeUnit {
                    locals: SignatureIndex(1), // empty
                    code: vec![
                        Bytecode::CopyLoc(0),                   // push x
                        Bytecode::Call(FunctionHandleIndex(1)), // Dep::double(x)
                        Bytecode::Ret,
                    ],
                    jump_tables: vec![],
                }),
            },
        ],
        signatures: vec![
            Signature(vec![SignatureToken::U64]), // 0: (u64) — params & return
            Signature(vec![]),                    // 1: empty locals
        ],
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
    };

    (dep, main)
}

#[test]
fn compile_cross_module_call() {
    let (dep, main) = make_cross_module_pair();
    let asm = move_to_llvm::compile_module_with_deps(&main, &[dep])
        .expect("cross-module compilation failed");

    assert!(
        asm.contains("call_double"),
        "assembly should contain 'call_double'\nassembly:\n{asm}"
    );
    // The call to Dep::double should appear as a `bl` instruction
    assert!(
        asm.contains("bl") && asm.contains("double"),
        "assembly should contain a 'bl' to 'double'\nassembly:\n{asm}"
    );
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_cross_module_call() {
    let (dep, main) = make_cross_module_pair();

    // Compile both modules separately
    let dep_asm = move_to_llvm::compile_module(&dep).expect("dep compilation failed");
    let main_asm =
        move_to_llvm::compile_module_with_deps(&main, &[dep]).expect("main compilation failed");

    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let dep_asm_path = temp_dir.path().join("dep.s");
    let main_asm_path = temp_dir.path().join("main.s");
    let dylib_ext = if cfg!(target_os = "macos") {
        "dylib"
    } else {
        "so"
    };
    let dylib_path = temp_dir.path().join(format!("test.{dylib_ext}"));

    std::fs::write(&dep_asm_path, &dep_asm).expect("failed to write dep asm");
    std::fs::write(&main_asm_path, &main_asm).expect("failed to write main asm");

    // Link both into one shared library
    let output = Command::new("cc")
        .args([
            "-shared",
            "-o",
            dylib_path.to_str().unwrap(),
            dep_asm_path.to_str().unwrap(),
            main_asm_path.to_str().unwrap(),
        ])
        .output()
        .expect("failed to run cc");
    assert!(
        output.status.success(),
        "cc failed to link cross-module dylib:\nstderr: {}",
        String::from_utf8_lossy(&output.stderr),
    );

    unsafe {
        let lib_path = CString::new(dylib_path.to_str().unwrap()).unwrap();
        let lib = libc::dlopen(lib_path.as_ptr(), libc::RTLD_NOW);
        if lib.is_null() {
            let err = std::ffi::CStr::from_ptr(libc::dlerror())
                .to_str()
                .unwrap_or("unknown error");
            panic!("dlopen failed: {err}");
        }

        let sym_name = CString::new("call_double").unwrap();
        let sym = libc::dlsym(lib, sym_name.as_ptr());
        if sym.is_null() {
            let err = std::ffi::CStr::from_ptr(libc::dlerror())
                .to_str()
                .unwrap_or("unknown error");
            libc::dlclose(lib);
            panic!("dlsym failed: {err}");
        }

        let f: unsafe extern "C" fn(u64) -> u64 = std::mem::transmute(sym);

        assert_eq!(f(5), 10, "call_double(5) should be 10");
        assert_eq!(f(0), 0, "call_double(0) should be 0");
        assert_eq!(f(100), 200, "call_double(100) should be 200");

        libc::dlclose(lib);
    }
}

// ---------------------------------------------------------------------------
// Generic function call tests (monomorphization)
// ---------------------------------------------------------------------------

/// Build a module with:
///   - `identity<T>(x: T): T { x }` — generic
///   - `call_identity(x: u64): u64 { identity<u64>(x) }` — via CallGeneric
fn make_generic_call_module() -> CompiledModule {
    CompiledModule {
        version: 7,
        publishable: true,
        self_module_handle_idx: ModuleHandleIndex(0),
        module_handles: vec![ModuleHandle {
            address: AddressIdentifierIndex(0),
            name: IdentifierIndex(0),
        }],
        identifiers: vec![
            Identifier::new("M").unwrap(),             // 0
            Identifier::new("identity").unwrap(),      // 1
            Identifier::new("call_identity").unwrap(), // 2
        ],
        address_identifiers: vec![AccountAddress::ZERO],
        function_handles: vec![
            // 0: identity<T>(x: T): T
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(1),
                parameters: SignatureIndex(0), // (T)
                return_: SignatureIndex(0),    // (T)
                type_parameters: vec![AbilitySet::EMPTY],
            },
            // 1: call_identity(x: u64): u64
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(2),
                parameters: SignatureIndex(1), // (u64)
                return_: SignatureIndex(1),    // (u64)
                type_parameters: vec![],
            },
        ],
        function_defs: vec![
            // identity<T>(x: T): T { x }
            FunctionDefinition {
                function: FunctionHandleIndex(0),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: Some(CodeUnit {
                    locals: SignatureIndex(2), // empty
                    code: vec![Bytecode::MoveLoc(0), Bytecode::Ret],
                    jump_tables: vec![],
                }),
            },
            // call_identity(x: u64): u64 { identity<u64>(x) }
            FunctionDefinition {
                function: FunctionHandleIndex(1),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: Some(CodeUnit {
                    locals: SignatureIndex(2), // empty
                    code: vec![
                        Bytecode::CopyLoc(0),
                        Bytecode::CallGeneric(FunctionInstantiationIndex(0)),
                        Bytecode::Ret,
                    ],
                    jump_tables: vec![],
                }),
            },
        ],
        signatures: vec![
            Signature(vec![SignatureToken::TypeParameter(0)]), // 0: (T)
            Signature(vec![SignatureToken::U64]),              // 1: (u64)
            Signature(vec![]),                                 // 2: empty locals
            Signature(vec![SignatureToken::U64]),              // 3: instantiation [U64]
        ],
        function_instantiations: vec![FunctionInstantiation {
            handle: FunctionHandleIndex(0),
            type_parameters: SignatureIndex(3), // [U64]
        }],
        struct_defs: vec![],
        datatype_handles: vec![],
        constant_pool: vec![],
        metadata: vec![],
        field_handles: vec![],
        friend_decls: vec![],
        struct_def_instantiations: vec![],
        field_instantiations: vec![],
        enum_defs: vec![],
        enum_def_instantiations: vec![],
        variant_handles: vec![],
        variant_instantiation_handles: vec![],
    }
}

#[test]
fn compile_generic_call() {
    let module = make_generic_call_module();
    let asm = move_to_llvm::compile_module(&module).expect("generic call compilation failed");

    assert!(
        asm.contains("identity"),
        "assembly should contain monomorphized 'identity' symbol\nassembly:\n{asm}"
    );
    assert!(
        asm.contains("call_identity"),
        "assembly should contain 'call_identity' symbol\nassembly:\n{asm}"
    );
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_generic_call() {
    let module = make_generic_call_module();
    let asm = move_to_llvm::compile_module(&module).expect("compilation failed");
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );

    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let obj_path = temp_dir.path().join("test.o");
    assemble(&asm, &obj_path);

    let call_identity_offset = find_symbol_offset(&obj_path, "call_identity");

    let code = extract_text_section(&obj_path);
    let exec = ExecutableCode::load(&code);

    type IdentityFn = unsafe extern "C" fn(u64) -> u64;
    let f: IdentityFn = unsafe { exec.as_fn_at(call_identity_offset as usize) };

    assert_eq!(unsafe { f(42) }, 42, "call_identity(42) should be 42");
    assert_eq!(unsafe { f(0) }, 0, "call_identity(0) should be 0");
    assert_eq!(
        unsafe { f(u64::MAX) },
        u64::MAX,
        "call_identity(MAX) should be MAX"
    );
}

// ---------------------------------------------------------------------------
// Address and U256 constant tests
// ---------------------------------------------------------------------------

#[test]
fn compile_address_constant() {
    // load_addr(): address { let a = @0x42; a }
    // Address constant: 32 bytes, big-endian, 0x42 in the last byte
    let mut addr_bytes = [0u8; 32];
    addr_bytes[31] = 0x42;
    let mut module = make_module(
        "load_addr",
        vec![],
        vec![SignatureToken::Address],
        vec![SignatureToken::Address],
        vec![
            Bytecode::LdConst(ConstantPoolIndex(0)),
            Bytecode::StLoc(0),
            Bytecode::MoveLoc(0),
            Bytecode::Ret,
        ],
    );
    module
        .constant_pool
        .push(move_binary_format::file_format::Constant {
            type_: SignatureToken::Address,
            data: addr_bytes.to_vec(), // BCS of AccountAddress = raw 32 bytes
        });
    let asm = move_to_llvm::compile_module(&module).expect("address constant compilation failed");
    assert!(
        asm.contains("load_addr"),
        "assembly should contain 'load_addr'\nassembly:\n{asm}"
    );
}

#[test]
fn compile_u256_constant() {
    // load_u256(): u256 { let x: u256 = 1000; x }
    // U256 constant: 32 bytes, little-endian
    let val: u64 = 1000;
    let mut u256_bytes = [0u8; 32];
    u256_bytes[..8].copy_from_slice(&val.to_le_bytes());
    let mut module = make_module(
        "load_u256",
        vec![],
        vec![SignatureToken::U256],
        vec![SignatureToken::U256],
        vec![
            Bytecode::LdConst(ConstantPoolIndex(0)),
            Bytecode::StLoc(0),
            Bytecode::MoveLoc(0),
            Bytecode::Ret,
        ],
    );
    module
        .constant_pool
        .push(move_binary_format::file_format::Constant {
            type_: SignatureToken::U256,
            data: u256_bytes.to_vec(), // BCS of U256 = 32 bytes LE
        });
    let asm = move_to_llvm::compile_module(&module).expect("u256 constant compilation failed");
    assert!(
        asm.contains("load_u256"),
        "assembly should contain 'load_u256'\nassembly:\n{asm}"
    );
}

// ---------------------------------------------------------------------------
// Address and Signer type tests
// ---------------------------------------------------------------------------

#[test]
fn compile_address_type() {
    // identity_addr(a: address): address { a }
    let module = make_module(
        "identity_addr",
        vec![SignatureToken::Address],
        vec![SignatureToken::Address],
        vec![],
        vec![Bytecode::CopyLoc(0), Bytecode::Ret],
    );
    let asm = move_to_llvm::compile_module(&module).expect("address compilation failed");
    assert!(
        asm.contains("identity_addr"),
        "assembly should contain 'identity_addr'\nassembly:\n{asm}"
    );
}

#[test]
fn compile_signer_type() {
    // identity_signer(s: signer): signer { s }
    let module = make_module(
        "identity_signer",
        vec![SignatureToken::Signer],
        vec![SignatureToken::Signer],
        vec![],
        vec![Bytecode::CopyLoc(0), Bytecode::Ret],
    );
    let asm = move_to_llvm::compile_module(&module).expect("signer compilation failed");
    assert!(
        asm.contains("identity_signer"),
        "assembly should contain 'identity_signer'\nassembly:\n{asm}"
    );
}

// ---------------------------------------------------------------------------
// Abort with error code test
// ---------------------------------------------------------------------------

#[test]
fn compile_abort_with_code() {
    // abort_42(): never { abort 42 }
    let module = make_module(
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
    );
    let asm = move_to_llvm::compile_module(&module).expect("abort compilation failed");
    assert!(
        asm.contains("__move_rt_abort"),
        "assembly should contain '__move_rt_abort' call\nassembly:\n{asm}"
    );
}

// ---------------------------------------------------------------------------
// Global storage operation tests
// ---------------------------------------------------------------------------

/// Build a module with a struct `Coin { value: u64 }` and storage operations.
fn make_storage_ops_module() -> CompiledModule {
    use move_binary_format::file_format::{
        AbilitySet, DatatypeHandle, DatatypeHandleIndex, FieldDefinition, StructDefinition,
        StructDefinitionIndex, StructFieldInformation, TypeSignature,
    };

    use move_binary_format::file_format::Ability;
    // Coin has key ability (required for global storage)
    let coin_abilities = AbilitySet::EMPTY | Ability::Key;

    CompiledModule {
        version: 7,
        publishable: true,
        self_module_handle_idx: ModuleHandleIndex(0),
        module_handles: vec![ModuleHandle {
            address: AddressIdentifierIndex(0),
            name: IdentifierIndex(0),
        }],
        identifiers: vec![
            Identifier::new("M").unwrap(),            // 0
            Identifier::new("Coin").unwrap(),         // 1
            Identifier::new("check_exists").unwrap(), // 2
            Identifier::new("take_coin").unwrap(),    // 3
            Identifier::new("publish_coin").unwrap(), // 4
            Identifier::new("borrow_coin").unwrap(),  // 5
            Identifier::new("value").unwrap(),        // 6
        ],
        address_identifiers: vec![AccountAddress::ZERO],
        datatype_handles: vec![DatatypeHandle {
            module: ModuleHandleIndex(0),
            name: IdentifierIndex(1),
            abilities: coin_abilities,
            type_parameters: vec![],
        }],
        struct_defs: vec![StructDefinition {
            struct_handle: DatatypeHandleIndex(0),
            field_information: StructFieldInformation::Declared(vec![FieldDefinition {
                name: IdentifierIndex(6),
                signature: TypeSignature(SignatureToken::U64),
            }]),
        }],
        function_handles: vec![
            // 0: check_exists(addr: address): bool
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(2),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(1),
                type_parameters: vec![],
            },
            // 1: take_coin(addr: address): Coin
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(3),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(2),
                type_parameters: vec![],
            },
            // 2: publish_coin(coin: Coin, signer: signer)
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(4),
                parameters: SignatureIndex(3),
                return_: SignatureIndex(4),
                type_parameters: vec![],
            },
            // 3: borrow_coin(addr: address): &Coin
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(5),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(5),
                type_parameters: vec![],
            },
        ],
        function_defs: vec![
            // check_exists(addr: address): bool { exists<Coin>(addr) }
            FunctionDefinition {
                function: FunctionHandleIndex(0),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: Some(CodeUnit {
                    locals: SignatureIndex(6),
                    code: vec![
                        Bytecode::CopyLoc(0),
                        Bytecode::ExistsDeprecated(StructDefinitionIndex(0)),
                        Bytecode::Ret,
                    ],
                    jump_tables: vec![],
                }),
            },
            // take_coin(addr: address): Coin { move_from<Coin>(addr) }
            FunctionDefinition {
                function: FunctionHandleIndex(1),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![StructDefinitionIndex(0)],
                code: Some(CodeUnit {
                    locals: SignatureIndex(6),
                    code: vec![
                        Bytecode::CopyLoc(0),
                        Bytecode::MoveFromDeprecated(StructDefinitionIndex(0)),
                        Bytecode::Ret,
                    ],
                    jump_tables: vec![],
                }),
            },
            // publish_coin(coin: Coin, signer: signer) { move_to<Coin>(signer, coin) }
            FunctionDefinition {
                function: FunctionHandleIndex(2),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: Some(CodeUnit {
                    locals: SignatureIndex(6),
                    code: vec![
                        Bytecode::MoveLoc(1), // push signer
                        Bytecode::MoveLoc(0), // push coin
                        Bytecode::MoveToDeprecated(StructDefinitionIndex(0)),
                        Bytecode::Ret,
                    ],
                    jump_tables: vec![],
                }),
            },
            // borrow_coin(addr: address): &Coin { borrow_global<Coin>(addr) }
            FunctionDefinition {
                function: FunctionHandleIndex(3),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![StructDefinitionIndex(0)],
                code: Some(CodeUnit {
                    locals: SignatureIndex(6),
                    code: vec![
                        Bytecode::CopyLoc(0),
                        Bytecode::ImmBorrowGlobalDeprecated(StructDefinitionIndex(0)),
                        Bytecode::Ret,
                    ],
                    jump_tables: vec![],
                }),
            },
        ],
        signatures: vec![
            Signature(vec![SignatureToken::Address]), // 0: (address)
            Signature(vec![SignatureToken::Bool]),    // 1: (bool)
            Signature(vec![SignatureToken::Datatype(DatatypeHandleIndex(0))]), // 2: (Coin)
            Signature(vec![
                SignatureToken::Datatype(DatatypeHandleIndex(0)),
                SignatureToken::Signer,
            ]), // 3: (Coin, signer)
            Signature(vec![]),                        // 4: ()
            Signature(vec![SignatureToken::Reference(Box::new(
                SignatureToken::Datatype(DatatypeHandleIndex(0)),
            ))]), // 5: (&Coin)
            Signature(vec![]),                        // 6: empty locals
        ],
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

#[test]
fn compile_global_storage_ops() {
    let module = make_storage_ops_module();
    let asm = move_to_llvm::compile_module(&module).expect("storage ops compilation failed");

    assert!(
        asm.contains("__move_rt_exists"),
        "assembly should contain '__move_rt_exists'\nassembly:\n{asm}"
    );
    assert!(
        asm.contains("__move_rt_move_from"),
        "assembly should contain '__move_rt_move_from'\nassembly:\n{asm}"
    );
    assert!(
        asm.contains("__move_rt_move_to"),
        "assembly should contain '__move_rt_move_to'\nassembly:\n{asm}"
    );
    assert!(
        asm.contains("__move_rt_borrow_global"),
        "assembly should contain '__move_rt_borrow_global'\nassembly:\n{asm}"
    );
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );
}

// ---------------------------------------------------------------------------
// Multi-return value tests
// ---------------------------------------------------------------------------

/// Build a module with `swap(a: u64, b: u64): (u64, u64)`.
fn make_multi_return_module() -> CompiledModule {
    make_module(
        "swap",
        vec![SignatureToken::U64, SignatureToken::U64],
        vec![SignatureToken::U64, SignatureToken::U64],
        vec![],
        vec![
            Bytecode::CopyLoc(1), // push b
            Bytecode::CopyLoc(0), // push a
            Bytecode::Ret,        // return (b, a)
        ],
    )
}

#[test]
fn compile_multi_return() {
    let module = make_multi_return_module();
    let asm = move_to_llvm::compile_module(&module).expect("multi-return compilation failed");

    assert!(
        asm.contains("swap"),
        "assembly should contain 'swap' symbol\nassembly:\n{asm}"
    );
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );
}

/// Build a module that calls a multi-return function:
///   - `swap(a: u64, b: u64): (u64, u64)` — returns (b, a)
///   - `test_swap(a: u64, b: u64): u64` — calls swap, returns first element (b)
fn make_multi_return_caller_module() -> CompiledModule {
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
            Identifier::new("swap").unwrap(),
            Identifier::new("test_swap").unwrap(),
        ],
        address_identifiers: vec![AccountAddress::ZERO],
        function_handles: vec![
            // 0: swap(u64, u64): (u64, u64)
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(1),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(0),
                type_parameters: vec![],
            },
            // 1: test_swap(u64, u64): u64
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(2),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(1),
                type_parameters: vec![],
            },
        ],
        function_defs: vec![
            // swap(a: u64, b: u64): (u64, u64) { (b, a) }
            FunctionDefinition {
                function: FunctionHandleIndex(0),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: Some(CodeUnit {
                    locals: SignatureIndex(2),
                    code: vec![
                        Bytecode::CopyLoc(1), // push b
                        Bytecode::CopyLoc(0), // push a
                        Bytecode::Ret,        // return (b, a)
                    ],
                    jump_tables: vec![],
                }),
            },
            // test_swap(a: u64, b: u64): u64
            // locals: [a, b, swapped_first, swapped_second]
            FunctionDefinition {
                function: FunctionHandleIndex(1),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: Some(CodeUnit {
                    locals: SignatureIndex(0), // [u64, u64]
                    code: vec![
                        Bytecode::CopyLoc(0),                   // push a
                        Bytecode::CopyLoc(1),                   // push b
                        Bytecode::Call(FunctionHandleIndex(0)), // swap(a, b)
                        Bytecode::StLoc(3),                     // swapped_second = a
                        Bytecode::StLoc(2),                     // swapped_first = b
                        Bytecode::MoveLoc(2),                   // push swapped_first
                        Bytecode::Ret,
                    ],
                    jump_tables: vec![],
                }),
            },
        ],
        signatures: vec![
            Signature(vec![SignatureToken::U64, SignatureToken::U64]), // 0: (u64, u64)
            Signature(vec![SignatureToken::U64]),                      // 1: (u64)
            Signature(vec![]),                                         // 2: empty locals
        ],
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

#[test]
fn compile_multi_return_caller() {
    let module = make_multi_return_caller_module();
    let asm =
        move_to_llvm::compile_module(&module).expect("multi-return caller compilation failed");

    assert!(
        asm.contains("swap"),
        "assembly should contain 'swap'\nassembly:\n{asm}"
    );
    assert!(
        asm.contains("test_swap"),
        "assembly should contain 'test_swap'\nassembly:\n{asm}"
    );
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_multi_return() {
    let module = make_multi_return_caller_module();
    let asm = move_to_llvm::compile_module(&module).expect("compilation failed");
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );

    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let obj_path = temp_dir.path().join("test.o");
    assemble(&asm, &obj_path);

    let test_swap_offset = find_symbol_offset(&obj_path, "test_swap");

    let code = extract_text_section(&obj_path);
    let exec = ExecutableCode::load(&code);

    type SwapFn = unsafe extern "C" fn(u64, u64) -> u64;
    let f: SwapFn = unsafe { exec.as_fn_at(test_swap_offset as usize) };

    // swap(10, 20) returns (20, 10); test_swap returns the first element (20)
    assert_eq!(
        unsafe { f(10, 20) },
        20,
        "test_swap(10, 20) should return 20 (first element of swapped result)"
    );
    assert_eq!(unsafe { f(0, 42) }, 42, "test_swap(0, 42) should return 42");
    assert_eq!(
        unsafe { f(100, 200) },
        200,
        "test_swap(100, 200) should return 200"
    );
}

// ---------------------------------------------------------------------------
// Vector constant tests
// ---------------------------------------------------------------------------

/// Build a module that loads a `vector<u8>` constant from the constant pool and returns it.
///
/// BCS encoding for `vector<u8>`: ULEB128 length prefix + raw bytes.
fn make_byte_array_const_module() -> CompiledModule {
    // BCS for vector<u8> [0x48, 0x65, 0x6C, 0x6C, 0x6F] = "Hello"
    let hello: Vec<u8> = b"Hello".to_vec();
    let mut bcs_data = Vec::new();
    bcs_data.push(hello.len() as u8); // ULEB128 length (5 fits in one byte)
    bcs_data.extend_from_slice(&hello);

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
            Identifier::new("get_bytes").unwrap(),
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
                code: vec![
                    Bytecode::LdConst(ConstantPoolIndex(0)),
                    Bytecode::StLoc(0),
                    Bytecode::MoveLoc(0),
                    Bytecode::Ret,
                ],
                jump_tables: vec![],
            }),
        }],
        signatures: vec![
            Signature(vec![]), // 0: params ()
            Signature(vec![SignatureToken::Vector(Box::new(SignatureToken::U8))]), // 1: return
            Signature(vec![SignatureToken::Vector(Box::new(SignatureToken::U8))]), // 2: locals
        ],
        constant_pool: vec![move_binary_format::file_format::Constant {
            type_: SignatureToken::Vector(Box::new(SignatureToken::U8)),
            data: bcs_data,
        }],
        struct_defs: vec![],
        datatype_handles: vec![],
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

#[test]
fn compile_byte_array_constant() {
    let module = make_byte_array_const_module();
    let asm =
        move_to_llvm::compile_module(&module).expect("byte array constant compilation failed");

    assert!(
        asm.contains("__move_rt_const_vec_u8"),
        "assembly should call __move_rt_const_vec_u8\nassembly:\n{asm}"
    );
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );
}

/// Build a module that loads a `vector<u64>` constant from the constant pool.
///
/// BCS encoding for `vector<u64>`: ULEB128 count + little-endian u64 elements.
fn make_vector_u64_const_module() -> CompiledModule {
    // vector<u64> [10, 20, 30]
    let elems: Vec<u64> = vec![10, 20, 30];
    let mut bcs_data = Vec::new();
    bcs_data.push(elems.len() as u8); // ULEB128 count
    for e in &elems {
        bcs_data.extend_from_slice(&e.to_le_bytes());
    }

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
            Identifier::new("get_vec").unwrap(),
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
                code: vec![
                    Bytecode::LdConst(ConstantPoolIndex(0)),
                    Bytecode::StLoc(0),
                    Bytecode::MoveLoc(0),
                    Bytecode::Ret,
                ],
                jump_tables: vec![],
            }),
        }],
        signatures: vec![
            Signature(vec![]), // 0: params ()
            Signature(vec![SignatureToken::Vector(Box::new(SignatureToken::U64))]), // 1: return
            Signature(vec![SignatureToken::Vector(Box::new(SignatureToken::U64))]), // 2: locals
        ],
        constant_pool: vec![move_binary_format::file_format::Constant {
            type_: SignatureToken::Vector(Box::new(SignatureToken::U64)),
            data: bcs_data,
        }],
        struct_defs: vec![],
        datatype_handles: vec![],
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

#[test]
fn compile_vector_u64_constant() {
    let module = make_vector_u64_const_module();
    let asm =
        move_to_llvm::compile_module(&module).expect("vector<u64> constant compilation failed");

    assert!(
        asm.contains("__move_rt_const_vec"),
        "assembly should call __move_rt_const_vec\nassembly:\n{asm}"
    );
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );
}
