//! Module storage abstraction
//!
//! Provides a trait for loading compiled modules from various sources:
//! - In-memory (testing, embedded modules)
//! - Database (future: RocksDB for blockchain state)

use std::{collections::HashMap, fmt::Debug, hash::Hash};

use crate::{
    CompiledModule,
    error::{RuntimeError, RuntimeResult},
};

/// Abstraction for compiled module storage
///
/// Implementations provide compiled modules from various sources.
/// The cache uses this trait to fetch modules on cache miss.
///
/// The associated `Id` type allows different stores to use different
/// identification schemes (filesystem paths, Move ModuleId, database keys, etc.).
pub trait ModuleStore: Send + Sync {
    /// The type used to identify modules in this store
    type Id: Clone + Eq + Hash + Send + Sync + 'static;

    /// Load a compiled module by ID
    fn load_module(&self, id: &Self::Id) -> RuntimeResult<CompiledModule>;
}

/// In-memory module store
///
/// Stores modules in a HashMap. Useful for testing and for cases where
/// modules are provided directly rather than loaded from disk.
#[derive(Default)]
pub struct MemoryStore<Id = String> {
    modules: HashMap<Id, CompiledModule>,
}

impl<Id: Clone + Eq + Hash> MemoryStore<Id> {
    /// Create a new empty memory store
    pub fn new() -> Self {
        Self {
            modules: HashMap::new(),
        }
    }

    /// Insert a module into the store
    pub fn insert(&mut self, id: Id, module: CompiledModule) {
        self.modules.insert(id, module);
    }

    /// Create a store with a single module
    pub fn with_module(id: Id, module: CompiledModule) -> Self {
        let mut store = Self::new();
        store.insert(id, module);
        store
    }
}

impl<Id> ModuleStore for MemoryStore<Id>
where
    Id: Clone + Eq + Hash + Send + Sync + Debug + 'static,
{
    type Id = Id;

    fn load_module(&self, id: &Self::Id) -> RuntimeResult<CompiledModule> {
        self.modules
            .get(id)
            .cloned()
            .ok_or_else(|| RuntimeError::ModuleNotFound {
                id: format!("{:?}", id as &dyn Debug),
            })
    }
}

#[cfg(test)]
pub mod mock {
    //! Mock store for testing cache behaviors
    //!
    //! Provides:
    //! - Pre-loaded modules (no filesystem access)
    //! - Load counters for deduplication verification
    //! - Failure injection for error handling tests
    //!
    //! MockStore is cheaply cloneable - clones share state.

    use std::{
        collections::HashMap,
        sync::{
            Arc, Mutex,
            atomic::{AtomicBool, AtomicU64, Ordering},
        },
    };

    use crate::{CompiledModule, ModuleStore, RuntimeError, RuntimeResult};

    /// Shared state for MockStore
    struct Inner {
        modules: Mutex<HashMap<usize, CompiledModule>>,
        load_count: AtomicU64,
        should_fail: AtomicBool,
        failure_reason: Mutex<Option<String>>,
    }

    /// Mock module store for testing
    ///
    /// Cloning shares state - useful for concurrent tests where you need
    /// to check `load_count()` after the cache has taken ownership.
    #[derive(Clone, Default)]
    pub struct MockStore {
        inner: Arc<Inner>,
    }

    impl Default for Inner {
        fn default() -> Self {
            Self {
                modules: Mutex::new(HashMap::new()),
                load_count: AtomicU64::new(0),
                should_fail: AtomicBool::new(false),
                failure_reason: Mutex::new(None),
            }
        }
    }

    impl MockStore {
        /// Create a new empty mock store
        pub fn new() -> Self {
            Self::default()
        }

        /// Add a module to the store
        pub fn add_module(&self, id: usize, module: CompiledModule) {
            self.inner.modules.lock().unwrap().insert(id, module);
        }

        /// Get total load count
        pub fn load_count(&self) -> u64 {
            self.inner.load_count.load(Ordering::SeqCst)
        }

        /// Configure next load to fail
        ///
        /// The next call to `load_module` will return an error.
        /// The failure is automatically cleared after triggering.
        pub fn fail_next(&self, reason: impl Into<String>) {
            self.inner.should_fail.store(true, Ordering::SeqCst);
            *self.inner.failure_reason.lock().unwrap() = Some(reason.into());
        }
    }

    impl ModuleStore for MockStore {
        type Id = usize;

        fn load_module(&self, id: &usize) -> RuntimeResult<CompiledModule> {
            // Increment counter first
            self.inner.load_count.fetch_add(1, Ordering::SeqCst);

            // Check for injected failure
            if self.inner.should_fail.swap(false, Ordering::SeqCst) {
                let reason = self
                    .inner
                    .failure_reason
                    .lock()
                    .unwrap()
                    .take()
                    .unwrap_or_else(|| "injected failure".into());
                return Err(RuntimeError::ModuleNotFound { id: reason });
            }

            // Return module
            self.inner
                .modules
                .lock()
                .unwrap()
                .get(id)
                .cloned()
                .ok_or_else(|| RuntimeError::ModuleNotFound {
                    id: format!("mock:{}", id),
                })
        }
    }
}
