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
