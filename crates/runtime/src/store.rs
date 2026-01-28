//! Module storage abstraction
//!
//! Provides a trait for loading compiled modules from various sources:
//! - In-memory (testing, embedded modules)
//! - Database (future: RocksDB for blockchain state)

use std::{collections::HashMap, hash::Hash};

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

impl<Id: Clone + Eq + Hash + Send + Sync + std::fmt::Debug + 'static> ModuleStore
    for MemoryStore<Id>
{
    type Id = Id;

    fn load_module(&self, id: &Self::Id) -> RuntimeResult<CompiledModule> {
        self.modules
            .get(id)
            .cloned()
            .ok_or_else(|| RuntimeError::ModuleNotFound {
                id: format!("{:?}", id as &dyn std::fmt::Debug),
            })
    }
}

#[cfg(test)]
pub mod mock {
    //! Mock store for testing concurrent cache behaviors
    //!
    //! Provides:
    //! - Pre-loaded modules (no filesystem access)
    //! - Load counters for deduplication verification
    //! - Configurable delays for race condition testing
    //! - Barriers for precise thread synchronization
    //! - Failure injection for error handling tests

    use std::{
        collections::HashMap,
        sync::{
            Arc,
            Barrier,
            Mutex,
            atomic::{AtomicBool, AtomicU64, Ordering},
        },
        thread,
        time::Duration,
    };

    use crate::{CompiledModule, ModuleStore, RuntimeError, RuntimeResult};

    pub struct MockStore {
        /// Pre-loaded modules by ID
        modules: Mutex<HashMap<usize, CompiledModule>>,
        /// Total load_module calls
        load_count: AtomicU64,
        /// Delay to inject on each load
        load_delay: Mutex<Option<Duration>>,
        /// Barrier to synchronize threads before load completes
        barrier: Mutex<Option<Arc<Barrier>>>,
        /// Whether next load should fail
        should_fail: AtomicBool,
        /// Custom failure message
        failure_reason: Mutex<Option<String>>,
    }

    impl MockStore {
        /// Create a new empty mock store
        pub fn new() -> Self {
            Self {
                modules: Mutex::new(HashMap::new()),
                load_count: AtomicU64::new(0),
                load_delay: Mutex::new(None),
                barrier: Mutex::new(None),
                should_fail: AtomicBool::new(false),
                failure_reason: Mutex::new(None),
            }
        }

        /// Add a module to the store
        pub fn add_module(&self, id: usize, module: CompiledModule) {
            self.modules.lock().unwrap().insert(id, module);
        }

        /// Get total load count
        pub fn load_count(&self) -> u64 {
            self.load_count.load(Ordering::SeqCst)
        }

        /// Set delay for load operations
        pub fn set_delay(&self, delay: Duration) {
            *self.load_delay.lock().unwrap() = Some(delay);
        }

        /// Set barrier for thread synchronization
        pub fn set_barrier(&self, barrier: Arc<Barrier>) {
            *self.barrier.lock().unwrap() = Some(barrier);
        }

        /// Configure next load to fail
        pub fn fail_next(&self, reason: impl Into<String>) {
            self.should_fail.store(true, Ordering::SeqCst);
            *self.failure_reason.lock().unwrap() = Some(reason.into());
        }

        /// Reset failure state
        #[allow(dead_code)]
        pub fn reset_failure(&self) {
            self.should_fail.store(false, Ordering::SeqCst);
            *self.failure_reason.lock().unwrap() = None;
        }
    }

    impl Default for MockStore {
        fn default() -> Self {
            Self::new()
        }
    }

    impl ModuleStore for MockStore {
        type Id = usize;

        fn load_module(&self, id: &usize) -> RuntimeResult<CompiledModule> {
            // Increment counter first
            self.load_count.fetch_add(1, Ordering::SeqCst);

            // Apply delay if configured
            if let Some(delay) = *self.load_delay.lock().unwrap() {
                thread::sleep(delay);
            }

            // Wait at barrier if set
            if let Some(barrier) = self.barrier.lock().unwrap().as_ref() {
                barrier.wait();
            }

            // Check for injected failure
            if self.should_fail.swap(false, Ordering::SeqCst) {
                let reason = self
                    .failure_reason
                    .lock()
                    .unwrap()
                    .take()
                    .unwrap_or_else(|| "injected failure".into());
                return Err(RuntimeError::ModuleNotFound { id: reason });
            }

            // Return module
            self.modules
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
