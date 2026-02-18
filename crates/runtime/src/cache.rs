// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Module cache backed by pre-allocated code slots
//!
//! Caches compiled modules in executable memory slots with LRU eviction.
//! Uses moka's concurrent cache for thread-safe access.
//!
//! # Architecture
//!
//! ```text
//! ModuleStore (persistent storage)
//!      ↓ fetch on cache miss
//! ModuleCache (LRU, backed by Pool/Slots)
//!      ↓
//! FunctionHandle → Executor
//! ```

use std::sync::Arc;

use moka::sync::Cache;

use crate::{
    error::{RuntimeError, RuntimeResult},
    module::{FunctionHandle, LoadedModule},
    slot::SlotPool,
    store::ModuleStore,
};

/// Cache for loaded modules backed by pre-allocated code slots
///
/// Generic over the module store type. Uses LRU eviction when the cache
/// is full to free slots for new modules.
///
/// # Thread Safety
///
/// This cache is thread-safe and can be shared across threads via `Arc<ModuleCache>`.
/// All methods take `&self` rather than `&mut self`.
///
/// # Lifetime Management
///
/// Each `FunctionHandle` holds an `Arc` reference to the loaded module.
/// The slot is only returned to the pool when:
/// 1. The module is evicted from the cache, AND
/// 2. All `FunctionHandle`s referencing that module are dropped
///
/// This ensures function pointers remain valid during execution.
pub struct ModuleCache<S: ModuleStore> {
    /// The backing store for loading module bytes
    store: S,
    /// Pool of pre-allocated code slots
    pool: SlotPool,
    /// LRU cache of loaded modules
    modules: Cache<S::Id, Arc<LoadedModule>>,
}

impl<S: ModuleStore> ModuleCache<S> {
    /// Create a new cache with the specified store and slot count
    ///
    /// Each slot has the default capacity (1 MB).
    pub fn new(store: S, slot_count: usize) -> RuntimeResult<Self> {
        Self::with_capacity(store, slot_count, crate::slot::DEFAULT_CODE_SIZE)
    }

    /// Create a new cache with custom slot capacity
    ///
    /// # Arguments
    ///
    /// * `store` - The backing store for loading module bytes
    /// * `slot_count` - Number of code slots to pre-allocate
    /// * `slot_capacity` - Size of each slot in bytes
    pub fn with_capacity(store: S, slot_count: usize, slot_capacity: usize) -> RuntimeResult<Self> {
        let pool = SlotPool::with_capacity(slot_count, slot_capacity)?;
        let modules = Cache::builder().max_capacity(slot_count as u64).build();

        Ok(Self {
            store,
            pool,
            modules,
        })
    }

    /// Get a function from a loaded module, loading on cache miss
    ///
    /// Returns a `FunctionHandle` that keeps the slot alive while in use.
    /// If all slots are in use, this method blocks until a slot becomes available.
    ///
    /// # Safety
    ///
    /// The caller must ensure the type parameter `F` matches the actual
    /// function signature at the named entry point.
    ///
    /// # Errors
    ///
    /// - `RuntimeError::ModuleNotFound` if the module doesn't exist in the store
    /// - `RuntimeError::FunctionNotFound` if the function doesn't exist in the module
    pub unsafe fn get_function<F: Copy>(
        &self,
        module_id: &S::Id,
        function_name: &str,
    ) -> RuntimeResult<FunctionHandle<F>> {
        // Try to get from cache first
        let module = if let Some(m) = self.modules.get(module_id) {
            m
        } else {
            // Cache miss - load from store
            let loaded = self.load_module(module_id)?;
            // TODO: Explore pre-allocating Arc storage to avoid heap allocation
            let loaded = Arc::new(loaded);
            self.modules.insert(module_id.clone(), Arc::clone(&loaded));
            loaded
        };

        // Look up function offset
        let offset = *module.entry_points.get(function_name).ok_or_else(|| {
            RuntimeError::FunctionNotFound {
                name: function_name.to_string(),
            }
        })?;

        Ok(FunctionHandle::new(module, offset))
    }

    /// Load a module from the store into a slot
    fn load_module(&self, module_id: &S::Id) -> RuntimeResult<LoadedModule> {
        // Fetch from store
        let compiled = self.store.load_module(module_id)?;

        // Acquire a slot (blocks if none available, providing back-pressure)
        let mut handle = self.pool.acquire();

        // Load code into slot
        // Safety: We trust the store to return valid, verified code
        unsafe {
            handle.load_code(&compiled.code)?;
        }

        Ok(LoadedModule {
            handle,
            entry_points: compiled.entry_points,
        })
    }

    /// Get the number of modules currently in the cache
    #[cfg(test)]
    pub fn len(&self) -> usize {
        // Moka's entry_count is eventually consistent; sync first
        self.modules.run_pending_tasks();
        self.modules.entry_count() as usize
    }

    /// Check if the cache is empty
    #[cfg(test)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the number of available slots in the pool
    #[cfg(test)]
    pub fn available_slots(&self) -> usize {
        self.pool.available()
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, sync::Arc};

    use crate::{CompiledModule, ModuleCache, RuntimeError, store::mock::MockStore};

    #[test]
    fn test_cache_creation() {
        let store = MockStore::new();
        let cache = ModuleCache::new(store, 4).unwrap();
        assert_eq!(cache.available_slots(), 4);
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_with_capacity() {
        let store = MockStore::new();
        let cache = ModuleCache::with_capacity(store, 2, 4096).unwrap();
        assert_eq!(cache.available_slots(), 2);
    }

    #[test]
    fn test_module_not_found() {
        let store = MockStore::new();
        let cache = ModuleCache::new(store, 4).unwrap();

        let result = unsafe { cache.get_function::<fn()>(&999, "main") };
        assert!(matches!(result, Err(RuntimeError::ModuleNotFound { .. })));
    }

    #[test]
    fn test_function_not_found() {
        let store = MockStore::new();
        store.add_module(0, CompiledModule::new_for_test(42, "main"));
        let cache = ModuleCache::new(store, 4).unwrap();

        let result = unsafe { cache.get_function::<fn()>(&0, "missing") };
        assert!(matches!(result, Err(RuntimeError::FunctionNotFound { .. })));
    }

    #[test]
    fn test_len_tracking() {
        let store = MockStore::new();
        store.add_module(0, CompiledModule::new_for_test(1, "main"));
        store.add_module(1, CompiledModule::new_for_test(2, "main"));
        let cache = ModuleCache::new(store, 4).unwrap();

        assert_eq!(cache.len(), 0);

        unsafe { cache.get_function::<fn()>(&0, "main").unwrap() };
        assert_eq!(cache.len(), 1);

        unsafe { cache.get_function::<fn()>(&1, "main").unwrap() };
        assert_eq!(cache.len(), 2);

        // Cache hit doesn't change len
        unsafe { cache.get_function::<fn()>(&0, "main").unwrap() };
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_cache_hit_no_extra_slot() {
        let store = MockStore::new();
        store.add_module(0, CompiledModule::new_for_test(42, "main"));
        let cache = ModuleCache::new(store, 4).unwrap();

        // First call loads the module
        let _h1 = unsafe { cache.get_function::<fn()>(&0, "main").unwrap() };
        assert_eq!(cache.available_slots(), 3);

        // Second call hits cache - no new slot consumed
        let _h2 = unsafe { cache.get_function::<fn()>(&0, "main").unwrap() };
        assert_eq!(cache.available_slots(), 3);
    }

    #[test]
    fn test_multiple_entry_points() {
        // foo: mov x0, #1; ret
        // bar: mov x0, #2; ret
        let code: Vec<u8> = [
            0x20, 0x00, 0x80, 0xd2, // mov x0, #1
            0xc0, 0x03, 0x5f, 0xd6, // ret
            0x40, 0x00, 0x80, 0xd2, // mov x0, #2
            0xc0, 0x03, 0x5f, 0xd6, // ret
        ]
        .to_vec();
        let entry_points = HashMap::from([("foo".to_string(), 0u32), ("bar".to_string(), 8u32)]);
        let module = CompiledModule::new(code, entry_points);

        let store = MockStore::new();
        store.add_module(0, module);
        let cache = ModuleCache::new(store, 4).unwrap();

        // Get both functions from same module - only one slot used
        let _foo = unsafe { cache.get_function::<fn()>(&0, "foo").unwrap() };
        assert_eq!(cache.available_slots(), 3);

        let _bar = unsafe { cache.get_function::<fn()>(&0, "bar").unwrap() };
        assert_eq!(cache.available_slots(), 3); // Still 3 - same module
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_code_exceeds_slot_capacity() {
        let large_code = vec![0u8; 1024];
        let module = CompiledModule::with_single_entry(large_code, "main");

        let store = MockStore::new();
        store.add_module(0, module);
        let cache = ModuleCache::with_capacity(store, 4, 512).unwrap();

        let result = unsafe { cache.get_function::<fn()>(&0, "main") };
        assert!(matches!(result, Err(RuntimeError::LoadError { .. })));
    }

    #[test]
    #[cfg(target_arch = "aarch64")]
    fn test_load_and_execute() {
        let store = MockStore::new();
        store.add_module(0, CompiledModule::new_for_test(42, "main"));
        let cache = ModuleCache::new(store, 4).unwrap();

        let handle = unsafe {
            cache
                .get_function::<extern "C" fn() -> u64>(&0, "main")
                .unwrap()
        };
        assert_eq!(handle.as_ptr()(), 42);
    }

    #[test]
    #[cfg(target_arch = "aarch64")]
    fn test_multiple_entry_points_execution() {
        // foo: mov x0, #1; ret
        // bar: mov x0, #2; ret
        let code: Vec<u8> = [
            0x20, 0x00, 0x80, 0xd2, // mov x0, #1
            0xc0, 0x03, 0x5f, 0xd6, // ret
            0x40, 0x00, 0x80, 0xd2, // mov x0, #2
            0xc0, 0x03, 0x5f, 0xd6, // ret
        ]
        .to_vec();
        let entry_points = HashMap::from([("foo".to_string(), 0u32), ("bar".to_string(), 8u32)]);
        let module = CompiledModule::new(code, entry_points);

        let store = MockStore::new();
        store.add_module(0, module);
        let cache = ModuleCache::new(store, 4).unwrap();

        let foo = unsafe {
            cache
                .get_function::<extern "C" fn() -> u64>(&0, "foo")
                .unwrap()
        };
        let bar = unsafe {
            cache
                .get_function::<extern "C" fn() -> u64>(&0, "bar")
                .unwrap()
        };

        assert_eq!(foo.as_ptr()(), 1);
        assert_eq!(bar.as_ptr()(), 2);
    }

    #[test]
    fn test_concurrent_different_modules() {
        let store = MockStore::new();
        for i in 0..8 {
            store.add_module(i, CompiledModule::new_for_test(i as u16, "main"));
        }

        let cache = Arc::new(ModuleCache::new(store.clone(), 8).unwrap());

        let handles: Vec<_> = (0..8)
            .map(|i| {
                let cache = Arc::clone(&cache);
                std::thread::spawn(move || unsafe {
                    cache.get_function::<fn()>(&i, "main").unwrap();
                })
            })
            .collect();

        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(cache.len(), 8);
        assert_eq!(store.load_count(), 8);
    }

    #[test]
    fn test_concurrent_same_module() {
        let store = MockStore::new();
        store.add_module(0, CompiledModule::new_for_test(42, "main"));

        let cache = Arc::new(ModuleCache::new(store.clone(), 4).unwrap());

        let handles: Vec<_> = (0..8)
            .map(|_| {
                let cache = Arc::clone(&cache);
                std::thread::spawn(move || unsafe {
                    cache.get_function::<fn()>(&0, "main").unwrap();
                })
            })
            .collect();

        for h in handles {
            h.join().unwrap();
        }

        // Only one slot used (moka deduplicates by key)
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.available_slots(), 3);
    }

    #[test]
    fn test_store_load_failure() {
        let store = MockStore::new();
        store.add_module(0, CompiledModule::new_for_test(42, "main"));
        store.fail_next("simulated failure");

        let cache = ModuleCache::new(store, 4).unwrap();

        // First call fails due to injected failure
        let result = unsafe { cache.get_function::<fn()>(&0, "main") };
        assert!(matches!(result, Err(RuntimeError::ModuleNotFound { .. })));
    }
}
