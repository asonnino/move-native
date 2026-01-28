//! macOS-specific Slot implementation using MAP_JIT

use std::ptr::NonNull;

use libc::{
    MAP_ANONYMOUS,
    MAP_FAILED,
    MAP_JIT,
    MAP_PRIVATE,
    PROT_EXEC,
    PROT_READ,
    PROT_WRITE,
    c_int,
    c_void,
    size_t,
};

use crate::error::{RuntimeError, RuntimeResult};

extern "C" {
    fn pthread_jit_write_protect_np(enabled: c_int);
    fn sys_icache_invalidate(start: *mut c_void, len: size_t);
}

/// A pre-allocated code slot for loading native code
///
/// On macOS, this uses MAP_JIT with W^X toggle via `pthread_jit_write_protect_np`.
pub struct Slot {
    /// Writable/executable mapping (same pointer, we toggle W^X)
    code_rw: NonNull<u8>,
    /// Executable mapping (same as code_rw on macOS)
    code_rx: NonNull<u8>,
    /// Maximum code size
    code_capacity: usize,
}

// Safety: Slot owns its memory mappings and doesn't share them
unsafe impl Send for Slot {}
unsafe impl Sync for Slot {}

impl Slot {
    /// Allocate a new code slot with the given code capacity
    ///
    /// Allocates a single MAP_JIT region that allows toggling between writable
    /// and executable modes via `pthread_jit_write_protect_np`.
    pub fn allocate(code_capacity: usize) -> RuntimeResult<Self> {
        // Allocate with MAP_JIT - allows toggling between writable and executable
        // On Apple Silicon, we need all three permissions and use pthread_jit_write_protect_np
        // to toggle between W and X modes
        let code = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                code_capacity,
                PROT_READ | PROT_WRITE | PROT_EXEC,
                MAP_PRIVATE | MAP_ANONYMOUS | MAP_JIT,
                -1,
                0,
            )
        };

        if code == MAP_FAILED {
            return Err(RuntimeError::LoadError {
                path: "<code-pool>".into(),
                reason: format!("mmap failed: {}", std::io::Error::last_os_error()),
            });
        }

        let code_ptr = NonNull::new(code as *mut u8).ok_or_else(|| RuntimeError::LoadError {
            path: "<code-pool>".into(),
            reason: "mmap returned null".into(),
        })?;

        Ok(Self {
            code_rw: code_ptr,
            code_rx: code_ptr, // Same pointer on macOS, we toggle W^X
            code_capacity,
        })
    }

    /// Load code into this slot
    ///
    /// Copies the code bytes to the writable mapping and flushes the icache.
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

        // Disable write protection (allow writing)
        pthread_jit_write_protect_np(0);

        // Copy code
        std::ptr::copy_nonoverlapping(code.as_ptr(), self.code_rw.as_ptr(), code.len());

        // Re-enable write protection (make executable)
        pthread_jit_write_protect_np(1);

        // Flush instruction cache
        sys_icache_invalidate(self.code_rx.as_ptr() as *mut c_void, code.len());

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
        debug_assert!(offset < self.code_capacity, "offset {offset} >= capacity {}", self.code_capacity);
        let ptr = self.code_rx.as_ptr().add(offset);
        std::mem::transmute_copy(&ptr)
    }

    /// Get the capacity of this slot
    pub fn capacity(&self) -> usize {
        self.code_capacity
    }
}

impl Drop for Slot {
    fn drop(&mut self) {
        unsafe {
            libc::munmap(self.code_rw.as_ptr() as *mut c_void, self.code_capacity);
        }
    }
}
