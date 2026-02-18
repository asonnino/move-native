// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

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

use std::time::Duration;

use crossbeam_channel::{Receiver, Sender, bounded};

use crate::error::RuntimeResult;

/// Default code region size: 1 MB per slot
pub const DEFAULT_CODE_SIZE: usize = 1 << 20;

/// Pool of pre-allocated code slots
///
/// Provides slot allocation with back-pressure for concurrent use.
/// When all slots are in use, `acquire()` blocks until a slot becomes available.
/// Slots are returned to the pool when their `SlotHandle` is dropped.
///
/// # Cloning
///
/// `SlotPool` is cheaply cloneable. Cloning creates another handle to the
/// **same** underlying pool, not a new pool. All clones share the same slots.
#[derive(Clone)]
pub struct SlotPool {
    tx: Sender<Slot>,
    rx: Receiver<Slot>,
}

impl SlotPool {
    /// Create a new code pool with the given number of slots
    ///
    /// Each slot has the default code capacity (1 MB).
    pub fn new(slot_count: usize) -> RuntimeResult<Self> {
        Self::with_capacity(slot_count, DEFAULT_CODE_SIZE)
    }

    /// Create a new code pool with custom slot capacity
    pub fn with_capacity(slot_count: usize, slot_capacity: usize) -> RuntimeResult<Self> {
        let (tx, rx) = bounded(slot_count);

        for _ in 0..slot_count {
            let slot = Slot::allocate(slot_capacity)?;
            tx.send(slot).expect("channel should have capacity");
        }

        Ok(Self { tx, rx })
    }

    /// Acquire a slot from the pool, blocking if none available
    ///
    /// Blocks until a slot becomes available. This provides natural
    /// back-pressure when all slots are in use.
    pub fn acquire(&self) -> SlotHandle {
        let slot = self.rx.recv().expect("channel should not be disconnected");
        SlotHandle::new(self.tx.clone(), slot)
    }

    /// Try to acquire a slot from the pool without blocking
    ///
    /// Returns `None` if all slots are in use.
    pub fn try_acquire(&self) -> Option<SlotHandle> {
        self.rx
            .try_recv()
            .ok()
            .map(|slot| SlotHandle::new(self.tx.clone(), slot))
    }

    /// Acquire a slot from the pool with a timeout
    ///
    /// Returns `None` if no slot becomes available within the timeout.
    pub fn acquire_timeout(&self, timeout: Duration) -> Option<SlotHandle> {
        self.rx
            .recv_timeout(timeout)
            .ok()
            .map(|slot| SlotHandle::new(self.tx.clone(), slot))
    }

    /// Get the total number of slots in the pool
    #[cfg(test)]
    pub fn capacity(&self) -> usize {
        self.tx.capacity().unwrap()
    }

    /// Get the number of available slots
    #[cfg(test)]
    pub fn available(&self) -> usize {
        self.rx.len()
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
pub struct SlotHandle {
    tx: Sender<Slot>,
    slot: Option<Slot>,
}

impl SlotHandle {
    fn new(tx: Sender<Slot>, slot: Slot) -> Self {
        Self {
            tx,
            slot: Some(slot),
        }
    }

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

impl Drop for SlotHandle {
    fn drop(&mut self) {
        let slot = self.slot.take().expect("slot already taken");
        // Return slot to pool - this unblocks any waiting acquire()
        // If the channel is disconnected (pool dropped), the slot is simply dropped
        let _ = self.tx.send(slot);
    }
}

#[cfg(test)]
mod tests {
    use std::{
        sync::{
            Arc,
            atomic::{AtomicBool, AtomicUsize, Ordering},
        },
        time::Duration,
    };

    use super::{Slot, SlotPool};

    #[test]
    fn test_slot_allocation() {
        let slot = Slot::allocate(4096).expect("allocation should succeed");
        assert_eq!(slot.capacity(), 4096);
    }

    #[test]
    fn test_pool_creation() {
        let pool = SlotPool::new(4).expect("pool creation should succeed");
        assert_eq!(pool.capacity(), 4);
        assert_eq!(pool.available(), 4);
    }

    #[test]
    fn test_slot_acquire_release() {
        let pool = SlotPool::new(2).expect("pool creation should succeed");
        assert_eq!(pool.available(), 2);

        let handle1 = pool.acquire();
        assert_eq!(pool.available(), 1);

        let handle2 = pool.acquire();
        assert_eq!(pool.available(), 0);

        // Pool exhausted (try_acquire returns None)
        assert!(pool.try_acquire().is_none());

        // Release one
        drop(handle1);
        assert_eq!(pool.available(), 1);

        // Can acquire again
        let _handle3 = pool.acquire();
        assert_eq!(pool.available(), 0);

        drop(handle2);
        assert_eq!(pool.available(), 1);
    }

    #[test]
    fn test_acquire_blocks_until_slot_available() {
        let pool = SlotPool::new(1).expect("pool creation should succeed");

        // Acquire the only slot
        let handle = pool.acquire();
        assert_eq!(pool.available(), 0);

        let pool_clone = pool.clone();
        let acquired = Arc::new(AtomicBool::new(false));
        let acquired_clone = Arc::clone(&acquired);

        // Spawn a thread that will block on acquire
        let thread = std::thread::spawn(move || {
            let _handle = pool_clone.acquire();
            acquired_clone.store(true, Ordering::SeqCst);
        });

        // Give the thread time to start and block
        std::thread::sleep(Duration::from_millis(50));
        assert!(!acquired.load(Ordering::SeqCst), "should be blocked");

        // Release the slot
        drop(handle);

        // Thread should now complete
        thread.join().expect("thread should not panic");
        assert!(acquired.load(Ordering::SeqCst), "should have acquired");
    }

    #[test]
    fn test_acquire_timeout() {
        let pool = SlotPool::new(1).expect("pool creation should succeed");

        // Acquire the only slot
        let _handle = pool.acquire();

        // Timeout should return None
        let result = pool.acquire_timeout(Duration::from_millis(10));
        assert!(result.is_none());
    }

    #[test]
    fn test_acquire_timeout_success() {
        let pool = SlotPool::new(1).expect("pool creation should succeed");

        // Acquire the only slot
        let handle = pool.acquire();

        let pool_clone = pool.clone();
        let thread = std::thread::spawn(move || {
            // Release after a short delay
            std::thread::sleep(Duration::from_millis(20));
            drop(handle);
        });

        // Should succeed within timeout
        let result = pool_clone.acquire_timeout(Duration::from_millis(100));
        assert!(result.is_some());

        thread.join().expect("thread should not panic");
    }

    #[test]
    #[cfg(target_arch = "aarch64")]
    fn test_code_execution() {
        let pool = SlotPool::new(4).expect("pool creation should succeed");
        let mut handle = pool.acquire();

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
        let pool = SlotPool::new(4).expect("pool creation should succeed");
        let mut handle = pool.acquire();

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
        let pool = SlotPool::with_capacity(1, 16).expect("pool creation should succeed");
        let mut handle = pool.acquire();

        let large_code = vec![0u8; 32]; // Larger than 16 byte capacity

        unsafe {
            let result = handle.load_code(&large_code);
            assert!(result.is_err());
        }
    }

    #[test]
    #[cfg(target_arch = "aarch64")]
    fn test_slot_reuse() {
        let pool = SlotPool::new(1).expect("pool creation should succeed");

        // First use: mov x0, #1; ret
        let mut handle = pool.acquire();
        unsafe {
            handle
                .load_code(&[0x20, 0x00, 0x80, 0xd2, 0xc0, 0x03, 0x5f, 0xd6])
                .unwrap();
            let f: extern "C" fn() -> u64 = handle.get_function(0);
            assert_eq!(f(), 1);
        }
        drop(handle);

        // Reuse same slot: mov x0, #2; ret
        let mut handle = pool.acquire();
        unsafe {
            handle
                .load_code(&[0x40, 0x00, 0x80, 0xd2, 0xc0, 0x03, 0x5f, 0xd6])
                .unwrap();
            let f: extern "C" fn() -> u64 = handle.get_function(0);
            assert_eq!(f(), 2);
        }
    }

    #[test]
    fn test_pool_concurrent_access() {
        let pool = SlotPool::with_capacity(8, 4096).expect("pool creation should succeed");
        let completed = Arc::new(AtomicUsize::new(0));

        let handles: Vec<_> = (0..8)
            .map(|_| {
                let pool = pool.clone();
                let completed = Arc::clone(&completed);
                std::thread::spawn(move || {
                    for _ in 0..10 {
                        let handle = pool.acquire();
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

    #[test]
    fn test_concurrent_blocking_stress() {
        // More threads than slots to test back-pressure
        let pool = SlotPool::with_capacity(4, 4096).expect("pool creation should succeed");
        let completed = Arc::new(AtomicUsize::new(0));

        let handles: Vec<_> = (0..16)
            .map(|_| {
                let pool = pool.clone();
                let completed = Arc::clone(&completed);
                std::thread::spawn(move || {
                    for _ in 0..5 {
                        let handle = pool.acquire();
                        // Simulate some work
                        std::thread::sleep(Duration::from_micros(100));
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
