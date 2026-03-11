// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Shared test infrastructure for integration tests.
//!
//! Provides helpers for assembling, loading, and executing compiled Move code
//! on aarch64 platforms.

use std::path::Path;
use std::process::Command;

use move_binary_format::CompiledModule;
use tempfile::TempDir;

/// Assembles the given assembly source into an object file.
pub fn assemble(source: &str, obj_path: &Path) {
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
pub fn extract_text_section(obj_path: &Path) -> Vec<u8> {
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

/// Find the byte offset of a symbol within the text section of an object file.
pub fn find_symbol_offset(obj_path: &Path, name: &str) -> u64 {
    use object::{Object, ObjectSection, ObjectSymbol};

    let data = std::fs::read(obj_path).expect("failed to read object file");
    let file = object::File::parse(&*data).expect("failed to parse object file");

    let candidates: Vec<String> = vec![name.to_string(), format!("_{name}")];

    for sym in file.symbols() {
        let sym_name = sym.name().unwrap_or("");
        if candidates.iter().any(|c| c == sym_name) {
            let section_idx = sym.section_index().expect("symbol has no section");
            let section = file
                .section_by_index(section_idx)
                .expect("bad section index");
            return sym.address() - section.address();
        }
    }
    panic!("symbol '{name}' not found in object file");
}

/// Compile a module and assert that x23 is not referenced.
pub fn compile_module_checked(module: &CompiledModule) -> String {
    let asm = move_to_llvm::compile_module(&move_to_llvm::Target::Aarch64, module)
        .expect("compilation failed");
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );
    asm.to_string()
}

/// Compile a module with dependencies and assert that x23 is not referenced.
pub fn compile_module_with_deps_checked(
    module: &CompiledModule,
    deps: &[CompiledModule],
) -> String {
    let asm = move_to_llvm::compile_module_with_deps(&move_to_llvm::Target::Aarch64, module, deps)
        .expect("compilation failed");
    assert!(
        !asm.contains("x23"),
        "compiler should not emit x23 (reserved register)\nassembly:\n{asm}"
    );
    asm.to_string()
}

// ---------------------------------------------------------------------------
// ExecutableCode: mmap-based JIT execution for aarch64 tests
// ---------------------------------------------------------------------------

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
pub struct ExecutableCode {
    ptr: *mut u8,
    len: usize,
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
impl ExecutableCode {
    /// Load machine code bytes into executable memory via mmap.
    ///
    /// Uses a two-step approach (write then mprotect) to satisfy macOS W^X policy.
    pub fn load(code: &[u8]) -> Self {
        use libc::{
            _SC_PAGESIZE, MAP_ANON, MAP_PRIVATE, PROT_EXEC, PROT_READ, PROT_WRITE, mmap, mprotect,
            sysconf,
        };
        use std::ptr;

        let page_size = unsafe { sysconf(_SC_PAGESIZE) } as usize;
        let len = (code.len() + page_size - 1) & !(page_size - 1);

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

        let ptr = ptr as *mut u8;
        unsafe { ptr::copy_nonoverlapping(code.as_ptr(), ptr, code.len()) };

        let rc = unsafe { mprotect(ptr as *mut libc::c_void, len, PROT_READ | PROT_EXEC) };
        assert_eq!(rc, 0, "mprotect failed");

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
    pub unsafe fn as_fn<F: Copy>(&self) -> F {
        assert!(
            std::mem::size_of::<F>() == std::mem::size_of::<*const ()>(),
            "F must be a function pointer"
        );
        unsafe { std::mem::transmute_copy(&self.ptr) }
    }

    /// Get a function pointer at a given byte offset into the loaded code.
    ///
    /// # Safety
    /// The caller must ensure `F` matches the ABI and signature of the code at `offset`.
    pub unsafe fn as_fn_at<F: Copy>(&self, offset: usize) -> F {
        assert!(
            std::mem::size_of::<F>() == std::mem::size_of::<*const ()>(),
            "F must be a function pointer"
        );
        let ptr = self.ptr.add(offset);
        unsafe { std::mem::transmute_copy(&ptr) }
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
pub fn compile_and_load(module: &CompiledModule) -> ExecutableCode {
    let asm = compile_module_checked(module);
    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let obj_path = temp_dir.path().join("test.o");
    assemble(&asm, &obj_path);
    let code = extract_text_section(&obj_path);
    ExecutableCode::load(&code)
}

/// Compile a module, assemble, and load — returning both the executable and the object path
/// (kept alive via TempDir) for symbol lookups.
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
pub fn compile_and_load_with_symbols(
    module: &CompiledModule,
) -> (ExecutableCode, std::path::PathBuf, TempDir) {
    let asm = compile_module_checked(module);
    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let obj_path = temp_dir.path().join("test.o");
    assemble(&asm, &obj_path);
    let code = extract_text_section(&obj_path);
    let exec = ExecutableCode::load(&code);
    (exec, obj_path, temp_dir)
}

/// Minimal C runtime implementing `0x1::vector` operations for u64.
///
/// Move's `&mut vector<T>` is a mutable reference: a pointer to the slot
/// holding the vector pointer (ptr-to-ptr).
pub const VEC_RUNTIME_C: &str = r#"
#include <stdlib.h>
#include <stdint.h>

typedef struct { uint64_t len; uint64_t cap; uint64_t* data; } Vec_u64;

void* __move_rt_0x1_vector_empty$u64(void) {
    Vec_u64* v = (Vec_u64*)malloc(sizeof(Vec_u64));
    v->len = 0;
    v->cap = 4;
    v->data = (uint64_t*)malloc(4 * sizeof(uint64_t));
    return v;
}

void __move_rt_0x1_vector_push_back$u64(void** vpp, uint64_t val) {
    Vec_u64* v = (Vec_u64*)*vpp;
    if (v->len >= v->cap) {
        v->cap *= 2;
        v->data = (uint64_t*)realloc(v->data, v->cap * sizeof(uint64_t));
    }
    v->data[v->len++] = val;
}

uint64_t __move_rt_0x1_vector_pop_back$u64(void** vpp) {
    Vec_u64* v = (Vec_u64*)*vpp;
    return v->data[--v->len];
}

void __move_rt_0x1_vector_destroy_empty$u64(void* vp) {
    Vec_u64* v = (Vec_u64*)vp;
    free(v->data);
    free(v);
}
"#;
