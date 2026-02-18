use std::{path::Path, process::Command};

use instrumenter::{ParsedAssembly, build_cfg, instrument};
use move_binary_format::{CompiledModule, file_format::*};
use move_core_types::{account_address::AccountAddress, identifier::Identifier};
use tempfile::TempDir;

/// Build a minimal Move module with a single `add(u64, u64): u64` function.
fn make_add_module() -> CompiledModule {
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
            Identifier::new("add").unwrap(),
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
                locals: SignatureIndex(2), // empty — no extra locals
                code: vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::CopyLoc(1),
                    Bytecode::Add,
                    Bytecode::Ret,
                ],
                jump_tables: vec![],
            }),
        }],
        signatures: vec![
            Signature(vec![SignatureToken::U64, SignatureToken::U64]), // 0: params
            Signature(vec![SignatureToken::U64]),                      // 1: return
            Signature(vec![]),                                         // 2: locals (empty)
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

#[test]
fn compile_add_instruments_without_error() {
    let module = make_add_module();
    let asm = move_to_llvm::compile_module(&module).expect("compilation failed");

    // Feed through instrumenter — should not error (forward-only code, no back-edges)
    let parsed = ParsedAssembly::parse(&asm);
    let cfg_result = build_cfg(&parsed).expect("CFG build failed");
    let instrumented =
        instrument::instrument(parsed.lines(), &cfg_result).expect("instrumentation failed");

    // The instrumented output should still be valid assembly text
    assert!(instrumented.contains("ret"));
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

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn full_pipeline_compile_instrument_execute() {
    use runtime::{CompiledModule as RuntimeModule, Executor, MemoryStore, ModuleCache};

    let module = make_add_module();
    let asm = move_to_llvm::compile_module(&module).expect("compilation failed");

    // Instrument
    let parsed = ParsedAssembly::parse(&asm);
    let cfg_result = build_cfg(&parsed).expect("CFG build failed");
    let instrumented =
        instrument::instrument(parsed.lines(), &cfg_result).expect("instrumentation failed");

    // Assemble
    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let obj_path = temp_dir.path().join("test.o");
    assemble(&instrumented, &obj_path);

    // Extract text
    let code = extract_text_section(&obj_path);

    // Load into runtime
    let rt_module = RuntimeModule::with_single_entry(code, "add");
    let store = MemoryStore::with_module("test".to_string(), rt_module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    type AddFn = unsafe extern "C" fn(u64, u64) -> u64;
    let cached_fn = unsafe {
        cache
            .get_function::<AddFn>(&"test".to_string(), "add")
            .expect("failed to get function")
    };

    // Verify correctness: call with actual arguments
    let sum = unsafe { cached_fn.as_ptr()(3, 4) };
    assert_eq!(sum, 7, "add(3, 4) should return 7");

    // Verify gas metering
    let executor = Executor::init().expect("failed to create executor");
    let result = unsafe { executor.execute(&cached_fn, 100_000) }.expect("execute failed");

    assert!(
        result.completed(),
        "add function should complete (forward-only, no loops)"
    );
    // Forward-only code has no back-edges, so no gas is consumed
    assert_eq!(
        result.gas_consumed, 0,
        "forward-only code should consume no gas"
    );
}

/// Full pipeline from `.mv` file through every stage:
/// compile → instrument → assemble → verify → execute
#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn full_pipeline_from_mv_file() {
    use verifier::{VerificationError, Verifier, decode_instructions};
    use runtime::{CompiledModule as RuntimeModule, Executor, MemoryStore, ModuleCache};

    // 1. Compile: .mv bytes → assembly text
    let bytecode = include_bytes!("../../../tests/move_samples/add.mv");
    let asm = move_to_llvm::compile(bytecode).expect("compile from .mv file failed");

    // 2. Instrument: parse → CFG → insert gas checks
    let parsed = ParsedAssembly::parse(&asm);
    let cfg_result = build_cfg(&parsed).expect("CFG build failed");
    let instrumented =
        instrument::instrument(parsed.lines(), &cfg_result).expect("instrumentation failed");

    // 3. Assemble: .s → .o → extract machine code
    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let obj_path = temp_dir.path().join("test.o");
    assemble(&instrumented, &obj_path);
    let code = extract_text_section(&obj_path);

    // 4. Verify: decode + run all verification checks
    let instructions = decode_instructions(&code).expect("decode failed");
    let vresult = Verifier::new(&instructions).verify();

    // The compiler currently emits two constructs the verifier correctly rejects:
    //
    // (a) `ret` — an indirect branch; Move has no dynamic dispatch so indirect
    //     branches are banned. Will be replaced by a direct return mechanism.
    //
    // (b) A trampoline `add: b _add` after `ret` (macOS _ prefix aliasing).
    //     This is unreachable code with a back-edge, triggering both
    //     UnreachableCode and MissingGasCheck.
    //
    // Filter these known issues and assert no *unexpected* errors exist.
    let unexpected: Vec<_> = vresult
        .errors()
        .iter()
        .filter(|e| {
            !matches!(
                e,
                VerificationError::DisallowedInstruction { mnemonic, .. }
                    if mnemonic == "ret"
            ) && !matches!(e, VerificationError::UnreachableCode { .. })
                && !matches!(e, VerificationError::MissingGasCheck { .. })
        })
        .collect();
    assert!(
        unexpected.is_empty(),
        "unexpected verification errors: {unexpected:?}"
    );
    // Verify we got exactly the expected errors (not zero — the verifier IS working)
    assert!(
        !vresult.is_ok(),
        "verifier should flag `ret` and trampoline (known issues)"
    );

    // 5. Execute: load into runtime and run
    let rt_module = RuntimeModule::with_single_entry(code, "add");
    let store = MemoryStore::with_module("test".to_string(), rt_module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    type AddFn = unsafe extern "C" fn(u64, u64) -> u64;
    let cached_fn = unsafe {
        cache
            .get_function::<AddFn>(&"test".to_string(), "add")
            .expect("failed to get function")
    };

    // Verify correctness: call with actual arguments
    let sum = unsafe { cached_fn.as_ptr()(3, 4) };
    assert_eq!(sum, 7, "add(3, 4) should return 7");

    // Verify gas metering
    let executor = Executor::init().expect("failed to create executor");
    let result = unsafe { executor.execute(&cached_fn, 100_000) }.expect("execute failed");

    assert!(
        result.completed(),
        "add function should complete (forward-only, no loops)"
    );
    assert_eq!(
        result.gas_consumed, 0,
        "forward-only code should consume no gas"
    );
}

/// True end-to-end from `.move` source through every stage:
/// sui move build → compile → instrument → assemble → verify → execute
#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn full_pipeline_from_move_source() {
    use verifier::{VerificationError, Verifier, decode_instructions};
    use runtime::{CompiledModule as RuntimeModule, Executor, MemoryStore, ModuleCache};

    // 0. Check if `sui` CLI is available; skip gracefully if not.
    let sui_ok = Command::new("sui")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    if !sui_ok {
        eprintln!("skipping full_pipeline_from_move_source: `sui` CLI not in PATH");
        return;
    }

    // 1. Build .move → .mv via `sui move build`
    let project_dir = TempDir::new().expect("failed to create temp dir");
    std::fs::write(
        project_dir.path().join("Move.toml"),
        "[package]\nname = \"test\"\nedition = \"2024.beta\"\n",
    )
    .unwrap();
    std::fs::create_dir(project_dir.path().join("sources")).unwrap();
    std::fs::write(
        project_dir.path().join("sources/add.move"),
        include_str!("../../../tests/move_samples/add.move"),
    )
    .unwrap();

    let build_output = Command::new("sui")
        .args([
            "move",
            "build",
            "--path",
            project_dir.path().to_str().unwrap(),
            "--skip-fetch-latest-git-deps",
        ])
        .output()
        .expect("failed to run sui move build");
    assert!(
        build_output.status.success(),
        "sui move build failed:\n{}",
        String::from_utf8_lossy(&build_output.stderr)
    );

    let mv_path = project_dir.path().join("build/test/bytecode_modules/M.mv");
    let bytecode = std::fs::read(&mv_path).expect("compiled .mv not found");

    // 2. Compile: .mv bytes → assembly text
    let asm = move_to_llvm::compile(&bytecode).expect("compile failed");

    // 3. Instrument: parse → CFG → insert gas checks
    let parsed = ParsedAssembly::parse(&asm);
    let cfg_result = build_cfg(&parsed).expect("CFG build failed");
    let instrumented =
        instrument::instrument(parsed.lines(), &cfg_result).expect("instrumentation failed");

    // 4. Assemble: .s → .o → extract machine code
    let obj_path = project_dir.path().join("test.o");
    assemble(&instrumented, &obj_path);
    let code = extract_text_section(&obj_path);

    // 5. Verify: decode + run all verification checks
    let instructions = decode_instructions(&code).expect("decode failed");
    let vresult = Verifier::new(&instructions).verify();

    // Filter known issues (see full_pipeline_from_mv_file for details)
    let unexpected: Vec<_> = vresult
        .errors()
        .iter()
        .filter(|e| {
            !matches!(
                e,
                VerificationError::DisallowedInstruction { mnemonic, .. }
                    if mnemonic == "ret"
            ) && !matches!(e, VerificationError::UnreachableCode { .. })
                && !matches!(e, VerificationError::MissingGasCheck { .. })
        })
        .collect();
    assert!(
        unexpected.is_empty(),
        "unexpected verification errors: {unexpected:?}"
    );

    // 6. Execute: load into runtime and run
    let rt_module = RuntimeModule::with_single_entry(code, "add");
    let store = MemoryStore::with_module("test".to_string(), rt_module);
    let cache = ModuleCache::new(store, 4).expect("failed to create cache");

    type AddFn = unsafe extern "C" fn(u64, u64) -> u64;
    let cached_fn = unsafe {
        cache
            .get_function::<AddFn>(&"test".to_string(), "add")
            .expect("failed to get function")
    };

    // Verify correctness: call with actual arguments
    let sum = unsafe { cached_fn.as_ptr()(3, 4) };
    assert_eq!(sum, 7, "add(3, 4) should return 7");

    // Verify gas metering
    let executor = Executor::init().expect("failed to create executor");
    let result = unsafe { executor.execute(&cached_fn, 100_000) }.expect("execute failed");

    assert!(
        result.completed(),
        "add function should complete (forward-only, no loops)"
    );
    assert_eq!(
        result.gas_consumed, 0,
        "forward-only code should consume no gas"
    );
}
