//! Code pool for loading and executing native code
//!
//! # Platform-Specific Implementation
//!
//! - **macOS**: Uses `MAP_JIT` with `pthread_jit_write_protect_np` for W^X toggle
//! - **Linux**: Uses `memfd_create` + dual `mmap` with different permissions
//!
//! # Hot Path
//!
//! Loading code is just `memcpy` + icache flush - no syscalls on the critical path.

// Platform-specific Slot implementations
#[cfg(target_os = "macos")]
mod macos;
#[cfg(target_os = "macos")]
pub use macos::Slot;

#[cfg(target_os = "linux")]
mod linux;
#[cfg(target_os = "linux")]
pub use linux::Slot;

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
compile_error!("Slot only supported on macOS and Linux");

use std::{collections::HashMap, sync::Arc};

use crossbeam_queue::ArrayQueue;

use crate::error::{RuntimeError, RuntimeResult};

/// Default code region size: 1 MB per slot
pub const DEFAULT_CODE_SIZE: usize = 1 << 20;

/// Inner state of the code pool
struct PoolInner {
    /// Lock-free queue of available slots
    free_slots: ArrayQueue<Slot>,
}

/// Pool of pre-allocated code slots
///
/// Provides lock-free slot allocation for concurrent use.
/// Slots are returned to the pool when their `Handle` is dropped.
#[derive(Clone)]
pub struct Pool(Arc<PoolInner>);

impl Pool {
    /// Create a new code pool with the given number of slots
    ///
    /// Each slot has the default code capacity (1 MB).
    pub fn new(num_slots: usize) -> RuntimeResult<Self> {
        Self::with_capacity(num_slots, DEFAULT_CODE_SIZE)
    }

    /// Create a new code pool with custom slot capacity
    pub fn with_capacity(num_slots: usize, code_capacity: usize) -> RuntimeResult<Self> {
        let free_slots = ArrayQueue::new(num_slots);

        for _ in 0..num_slots {
            let slot = Slot::allocate(code_capacity)?;
            free_slots
                .push(slot)
                .ok()
                .expect("free_slots should have capacity");
        }

        Ok(Self(Arc::new(PoolInner { free_slots })))
    }

    /// Acquire a slot from the pool
    ///
    /// Returns `None` if all slots are in use.
    pub fn try_acquire(&self) -> Option<Handle> {
        let slot = self.0.free_slots.pop()?;
        Some(Handle {
            pool: Arc::clone(&self.0),
            slot: Some(slot),
        })
    }

    /// Acquire a slot from the pool
    ///
    /// Returns an error if all slots are currently in use.
    pub fn acquire(&self) -> RuntimeResult<Handle> {
        self.try_acquire().ok_or_else(|| RuntimeError::LoadError {
            path: "<code-pool>".into(),
            reason: "code pool exhausted".into(),
        })
    }

    /// Get the total number of slots in the pool
    #[cfg(test)]
    pub fn capacity(&self) -> usize {
        self.0.free_slots.capacity()
    }

    /// Get the number of available slots
    #[cfg(test)]
    pub fn available(&self) -> usize {
        self.0.free_slots.len()
    }
}

/// Owned handle to a code slot
///
/// Provides exclusive access to a slot from the pool. When dropped, the slot
/// is returned to the pool and can be reused by another caller.
///
/// # Slot Reuse
///
/// When a slot is reused, the previous code is simply overwritten.
pub struct Handle {
    pool: Arc<PoolInner>,
    slot: Option<Slot>,
}

impl Handle {
    /// Load code into this slot
    ///
    /// Overwrites any previously loaded code.
    ///
    /// # Safety
    ///
    /// The caller must ensure the code is valid, verified Arm64 machine code.
    pub unsafe fn load_code(&mut self, code: &[u8]) -> RuntimeResult<()> {
        self.slot.as_mut().unwrap().load_code(code)
    }

    /// Get a function pointer at the given offset
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `offset` is within the loaded code range
    /// - The type `F` matches the actual function signature
    pub unsafe fn get_function<F: Copy>(&self, offset: usize) -> F {
        self.slot.as_ref().unwrap().get_function(offset)
    }

    /// Get the slot's code capacity
    #[cfg(test)]
    pub fn capacity(&self) -> usize {
        self.slot.as_ref().unwrap().capacity()
    }
}

impl Drop for Handle {
    fn drop(&mut self) {
        let slot = self.slot.take().expect("slot already taken");
        self.pool
            .free_slots
            .push(slot)
            .ok()
            .expect("free_slots should have space for returned slot");
    }
}

/// Compiled module output from the compiler
///
/// Contains raw executable bytes and entry point offsets.
/// This is what gets stored in the database/cache.
#[derive(Clone, Debug)]
pub struct CompiledModule {
    /// Raw executable bytes (flat binary, no ELF wrapper)
    pub code: Vec<u8>,
    /// Function name -> offset in code
    pub entry_points: HashMap<String, u32>,
}

impl CompiledModule {
    /// Create a new compiled module
    pub fn new(code: Vec<u8>, entry_points: HashMap<String, u32>) -> Self {
        Self { code, entry_points }
    }

    /// Create a compiled module with a single entry point at offset 0
    pub fn with_single_entry(code: Vec<u8>, name: impl Into<String>) -> Self {
        Self::new(code, HashMap::from([(name.into(), 0)]))
    }
}

#[cfg(test)]
mod tests {
    use std::sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    };

    use crate::{CompiledModule, Pool, Slot};

    #[test]
    fn test_slot_allocation() {
        let slot = Slot::allocate(4096).expect("allocation should succeed");
        assert_eq!(slot.capacity(), 4096);
    }

    #[test]
    fn test_pool_creation() {
        let pool = Pool::new(4).expect("pool creation should succeed");
        assert_eq!(pool.capacity(), 4);
        assert_eq!(pool.available(), 4);
    }

    #[test]
    fn test_slot_acquire_release() {
        let pool = Pool::new(2).expect("pool creation should succeed");
        assert_eq!(pool.available(), 2);

        let handle1 = pool.acquire().expect("should acquire slot");
        assert_eq!(pool.available(), 1);

        let handle2 = pool.acquire().expect("should acquire slot");
        assert_eq!(pool.available(), 0);

        // Pool exhausted
        assert!(pool.try_acquire().is_none());

        // Release one
        drop(handle1);
        assert_eq!(pool.available(), 1);

        // Can acquire again
        let _handle3 = pool.acquire().expect("should acquire slot");
        assert_eq!(pool.available(), 0);

        drop(handle2);
        assert_eq!(pool.available(), 1);
    }

    #[test]
    #[cfg(target_arch = "aarch64")]
    fn test_code_execution() {
        let pool = Pool::new(4).expect("pool creation should succeed");
        let mut handle = pool.acquire().expect("should acquire slot");

        // Minimal Arm64: mov x0, #42; ret
        // 0xd2800540 = mov x0, #42
        // 0xd65f03c0 = ret
        let code: &[u8] = &[0x40, 0x05, 0x80, 0xd2, 0xc0, 0x03, 0x5f, 0xd6];

        unsafe {
            handle.load_code(code).expect("load should succeed");
            let func: extern "C" fn() -> u64 = handle.get_function(0);
            assert_eq!(func(), 42);
        }
    }

    #[test]
    #[cfg(target_arch = "aarch64")]
    fn test_code_execution_with_arguments() {
        let pool = Pool::new(4).expect("pool creation should succeed");
        let mut handle = pool.acquire().expect("should acquire slot");

        // add x0, x0, x1; ret
        // 0x8b010000 = add x0, x0, x1
        // 0xd65f03c0 = ret
        let code: &[u8] = &[0x00, 0x00, 0x01, 0x8b, 0xc0, 0x03, 0x5f, 0xd6];

        unsafe {
            handle.load_code(code).expect("load should succeed");
            let func: extern "C" fn(u64, u64) -> u64 = handle.get_function(0);
            assert_eq!(func(10, 32), 42);
        }
    }

    #[test]
    fn test_code_too_large() {
        let pool = Pool::with_capacity(1, 16).expect("pool creation should succeed");
        let mut handle = pool.acquire().expect("should acquire slot");

        let large_code = vec![0u8; 32]; // Larger than 16 byte capacity

        unsafe {
            let result = handle.load_code(&large_code);
            assert!(result.is_err());
        }
    }

    #[test]
    fn test_compiled_module() {
        let code = vec![0x40, 0x05, 0x80, 0xd2, 0xc0, 0x03, 0x5f, 0xd6];
        let module = CompiledModule::with_single_entry(code.clone(), "main");

        assert_eq!(module.code, code);
        assert_eq!(module.entry_points.get("main"), Some(&0));
    }

    #[test]
    fn test_pool_concurrent_access() {
        let pool = Pool::with_capacity(8, 4096).expect("pool creation should succeed");
        let completed = Arc::new(AtomicUsize::new(0));

        let handles: Vec<_> = (0..8)
            .map(|_| {
                let pool = pool.clone();
                let completed = Arc::clone(&completed);
                std::thread::spawn(move || {
                    for _ in 0..10 {
                        let handle = pool.acquire().expect("should acquire slot");
                        assert!(handle.capacity() > 0);
                        drop(handle);
                        completed.fetch_add(1, Ordering::Relaxed);
                    }
                })
            })
            .collect();

        for h in handles {
            h.join().expect("thread should not panic");
        }

        assert_eq!(completed.load(Ordering::Relaxed), 80);
    }
}
