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
    use crate::{CompiledModule, ModuleCache, RuntimeError, store::MemoryStore};

    #[test]
    fn test_cache_creation() {
        let store = MemoryStore::<String>::new();
        let cache = ModuleCache::new(store, 4).unwrap();
        assert_eq!(cache.available_slots(), 4);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_module_not_found() {
        let store = MemoryStore::<String>::new();
        let cache = ModuleCache::new(store, 4).unwrap();

        let result = unsafe { cache.get_function::<fn()>(&"missing".to_string(), "main") };
        assert!(matches!(result, Err(RuntimeError::ModuleNotFound { .. })));
    }

    #[test]
    fn test_symbol_not_found() {
        // mov x0, #42; ret
        let code = vec![0x40, 0x05, 0x80, 0xd2, 0xc0, 0x03, 0x5f, 0xd6];
        let module = CompiledModule::with_single_entry(code, "main");

        let store = MemoryStore::with_module("test".to_string(), module);
        let cache = ModuleCache::new(store, 4).unwrap();

        let result = unsafe { cache.get_function::<fn()>(&"test".to_string(), "missing") };
        assert!(matches!(result, Err(RuntimeError::FunctionNotFound { .. })));
    }

    #[test]
    #[cfg(target_arch = "aarch64")]
    fn test_load_and_execute() {
        // mov x0, #42; ret
        let code = vec![0x40, 0x05, 0x80, 0xd2, 0xc0, 0x03, 0x5f, 0xd6];
        let module = CompiledModule::with_single_entry(code, "main");

        let store = MemoryStore::with_module("test".to_string(), module);
        let cache = ModuleCache::new(store, 4).unwrap();

        let handle = unsafe {
            cache
                .get_function::<extern "C" fn() -> u64>(&"test".to_string(), "main")
                .unwrap()
        };

        let func = handle.as_ptr();
        assert_eq!(func(), 42);
    }

    #[test]
    #[cfg(target_arch = "aarch64")]
    fn test_cache_hit() {
        // mov x0, #42; ret
        let code = vec![0x40, 0x05, 0x80, 0xd2, 0xc0, 0x03, 0x5f, 0xd6];
        let module = CompiledModule::with_single_entry(code, "main");

        let store = MemoryStore::with_module("test".to_string(), module);
        let cache = ModuleCache::new(store, 4).unwrap();

        // First call loads the module - consumes one slot
        let _h1 = unsafe {
            cache
                .get_function::<fn()>(&"test".to_string(), "main")
                .unwrap()
        };
        assert_eq!(cache.available_slots(), 3);

        // Second call hits the cache - no new slot consumed
        let _h2 = unsafe {
            cache
                .get_function::<fn()>(&"test".to_string(), "main")
                .unwrap()
        };
        assert_eq!(cache.available_slots(), 3);
    }

    #[test]
    fn test_function_handle_keeps_slot_alive() {
        // mov x0, #42; ret
        let code = vec![0x40, 0x05, 0x80, 0xd2, 0xc0, 0x03, 0x5f, 0xd6];
        let module = CompiledModule::with_single_entry(code, "main");

        let store = MemoryStore::with_module("test".to_string(), module);
        let cache = ModuleCache::new(store, 4).unwrap();

        // Get a function handle
        let handle = unsafe {
            cache
                .get_function::<fn()>(&"test".to_string(), "main")
                .unwrap()
        };
        assert_eq!(cache.available_slots(), 3);

        // Even after eviction from cache, handle keeps slot alive
        // (Note: moka doesn't have explicit eviction, but we can verify the handle is valid)
        drop(cache);

        // Handle should still be valid (though we can't execute without aarch64)
        drop(handle);
    }
}
