// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Linux-specific Slot implementation using memfd + dual mmap

use std::{ffi::CString, os::unix::io::RawFd, ptr::NonNull};

use libc::{
    MAP_FAILED, MAP_SHARED, PROT_EXEC, PROT_READ, PROT_WRITE, c_char, c_uint, c_void, off_t,
};

use crate::error::{RuntimeError, RuntimeResult};

extern "C" {
    fn memfd_create(name: *const c_char, flags: c_uint) -> RawFd;
    fn __clear_cache(start: *mut c_void, end: *mut c_void);
}

/// memfd_create flags
const MFD_CLOEXEC: c_uint = 0x0001;

/// A pre-allocated code slot for loading native code
///
/// On Linux, this uses `memfd_create` + dual `mmap` with different permissions
/// (RW for writing, RX for execution) backed by the same memory.
pub struct Slot {
    /// Writable mapping for loading code
    code_rw: NonNull<u8>,
    /// Executable mapping (same backing memory)
    code_rx: NonNull<u8>,
    /// File descriptor for the code region
    code_fd: RawFd,
    /// Maximum code size
    code_capacity: usize,
}

// Safety: Slot owns its memory mappings and doesn't share them.
// Sync is safe because:
// - load_code takes &mut self (exclusive access enforced by borrow checker)
// - get_function takes &self and is read-only
unsafe impl Send for Slot {}
unsafe impl Sync for Slot {}

impl Slot {
    /// Allocate a new code slot with the given code capacity
    ///
    /// Creates a memfd and maps it twice: once RW for writing code,
    /// once RX for execution.
    pub fn allocate(code_capacity: usize) -> RuntimeResult<Self> {
        // Create anonymous file descriptor
        let name = CString::new("move-code").unwrap();
        let code_fd = unsafe { memfd_create(name.as_ptr(), MFD_CLOEXEC) };
        if code_fd < 0 {
            return Err(RuntimeError::LoadError {
                path: "<code-pool>".into(),
                reason: format!("memfd_create failed: {}", std::io::Error::last_os_error()),
            });
        }

        // Set size
        if unsafe { libc::ftruncate(code_fd, code_capacity as off_t) } < 0 {
            unsafe { libc::close(code_fd) };
            return Err(RuntimeError::LoadError {
                path: "<code-pool>".into(),
                reason: format!("ftruncate failed: {}", std::io::Error::last_os_error()),
            });
        }

        // Map RW (for writing code)
        let code_rw = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                code_capacity,
                PROT_READ | PROT_WRITE,
                MAP_SHARED,
                code_fd,
                0,
            )
        };

        if code_rw == MAP_FAILED {
            unsafe { libc::close(code_fd) };
            return Err(RuntimeError::LoadError {
                path: "<code-pool>".into(),
                reason: format!("mmap RW failed: {}", std::io::Error::last_os_error()),
            });
        }

        // Map RX (for execution) - same backing memory
        let code_rx = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                code_capacity,
                PROT_READ | PROT_EXEC,
                MAP_SHARED,
                code_fd,
                0,
            )
        };

        if code_rx == MAP_FAILED {
            unsafe {
                libc::munmap(code_rw, code_capacity);
                libc::close(code_fd);
            }
            return Err(RuntimeError::LoadError {
                path: "<code-pool>".into(),
                reason: format!("mmap RX failed: {}", std::io::Error::last_os_error()),
            });
        }

        // Safety: mmap returns MAP_FAILED (-1) on error, never null.
        // We already checked for MAP_FAILED above, so this is a valid non-null pointer.
        let code_rw_ptr = unsafe { NonNull::new_unchecked(code_rw as *mut u8) };
        let code_rx_ptr = unsafe { NonNull::new_unchecked(code_rx as *mut u8) };

        Ok(Self {
            code_rw: code_rw_ptr,
            code_rx: code_rx_ptr,
            code_fd,
            code_capacity,
        })
    }

    /// Load code into this slot
    ///
    /// Copies the code bytes to the RW mapping and flushes the icache.
    ///
    /// The code should have passed the native verifier (instruction whitelist,
    /// gas instrumentation checks) before being loaded.
    ///
    /// # Safety
    ///
    /// The caller must ensure `code` contains valid Arm64 machine code.
    /// Executing invalid or malicious machine code is undefined behavior.
    pub unsafe fn load_code(&mut self, code: &[u8]) -> RuntimeResult<()> {
        if code.len() > self.code_capacity {
            return Err(RuntimeError::LoadError {
                path: "<code-pool>".into(),
                reason: format!(
                    "code size {} exceeds capacity {}",
                    code.len(),
                    self.code_capacity
                ),
            });
        }

        // Copy code to RW mapping
        std::ptr::copy_nonoverlapping(code.as_ptr(), self.code_rw.as_ptr(), code.len());

        // Flush instruction cache (RX mapping will see the updated code)
        __clear_cache(
            self.code_rx.as_ptr() as *mut c_void,
            self.code_rx.as_ptr().add(code.len()) as *mut c_void,
        );

        Ok(())
    }

    /// Get a function pointer at the given offset in the code region
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `offset` is within the loaded code range
    /// - The type `F` matches the actual function signature at that offset
    /// - The code at that offset is a valid function entry point
    pub unsafe fn get_function<F: Copy>(&self, offset: usize) -> F {
        debug_assert!(
            offset < self.code_capacity,
            "offset {offset} >= capacity {}",
            self.code_capacity
        );
        let ptr = self.code_rx.as_ptr().add(offset);
        std::mem::transmute_copy(&ptr)
    }

    /// Get the capacity of this slot
    #[cfg(test)]
    pub fn capacity(&self) -> usize {
        self.code_capacity
    }
}

impl Drop for Slot {
    fn drop(&mut self) {
        unsafe {
            libc::munmap(self.code_rw.as_ptr() as *mut c_void, self.code_capacity);
            libc::munmap(self.code_rx.as_ptr() as *mut c_void, self.code_capacity);
            libc::close(self.code_fd);
        }
    }
}
