//! Module storage abstraction
//!
//! Provides a trait for loading module bytes from various sources:
//! - Filesystem (development, current integration tests)
//! - In-memory (unit testing with mocks)
//! - Database (future: RocksDB for blockchain state)

use std::{hash::Hash, io::Write, path::PathBuf, sync::Arc};

use crate::{
    NativeModule,
    error::{RuntimeError, RuntimeResult},
};

/// Abstraction for module byte storage
///
/// Implementations provide module bytes from various sources.
/// The cache uses this trait to fetch bytes, then delegates to
/// `NativeModule::load_from_bytes()` for actual loading.
///
/// The associated `Id` type allows different stores to use different
/// identification schemes (filesystem paths, Move ModuleId, database keys, etc.).
pub trait ModuleStore: Send + Sync {
    /// The type used to identify modules in this store
    type Id: Clone + Eq + Hash + Send + Sync + 'static;

    /// Load module bytes by ID into the provided writer
    ///
    /// Writes the raw bytes of the compiled native module to `writer`.
    fn load_bytes(&self, id: &Self::Id, writer: &mut impl Write) -> RuntimeResult<()>;

    /// Load a module by ID
    ///
    /// The caller provides a reusable buffer. Call `buffer.clear()` before
    /// calling this method if you want to reuse an existing buffer.
    fn load_module(
        &self,
        id: &Self::Id,
        buffer: &mut Vec<u8>,
    ) -> RuntimeResult<Arc<NativeModule>> {
        self.load_bytes(id, buffer)?;
        NativeModule::load_from_bytes(buffer)
    }
}

/// Filesystem-backed module store
///
/// Loads modules from disk paths. The `ModuleId` must contain a valid
/// filesystem path.
#[derive(Default, Clone)]
pub struct FileSystemStore;

impl FileSystemStore {
    /// Create a new filesystem store
    pub fn new() -> Self {
        Self
    }
}

impl ModuleStore for FileSystemStore {
    type Id = PathBuf;

    fn load_bytes(&self, id: &PathBuf, writer: &mut impl Write) -> RuntimeResult<()> {
        let bytes = std::fs::read(id).map_err(|e| RuntimeError::LoadError {
            path: id.clone(),
            reason: e.to_string(),
        })?;
        writer
            .write_all(&bytes)
            .map_err(|e| RuntimeError::LoadError {
                path: id.clone(),
                reason: e.to_string(),
            })
    }

    fn load_module(&self, id: &PathBuf, _buffer: &mut Vec<u8>) -> RuntimeResult<Arc<NativeModule>> {
        // FileSystemStore bypasses the buffer and loads directly from file
        NativeModule::load_from_file(id)
    }
}

/// Mock store for testing concurrent cache behaviors
///
/// Provides:
/// - Pre-loaded module bytes (no filesystem access)
/// - Load counters for deduplication verification
/// - Configurable delays for race condition testing
/// - Barriers for precise thread synchronization
/// - Failure injection for error handling tests
#[cfg(test)]
pub mod mock {

    use std::{
        collections::HashMap,
        path::PathBuf,
        sync::{
            Arc,
            Barrier,
            Mutex,
            atomic::{AtomicBool, AtomicU64, Ordering},
        },
        thread,
        time::Duration,
    };

    use crate::{ModuleStore, RuntimeError, RuntimeResult};

    pub struct MockStore {
        /// Pre-loaded module bytes by ID
        modules: Mutex<HashMap<usize, Vec<u8>>>,
        /// Total load_bytes calls
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
        pub fn add_module(&self, id: usize, bytes: Vec<u8>) {
            self.modules.lock().unwrap().insert(id, bytes);
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

        fn load_bytes(&self, id: &usize, writer: &mut impl std::io::Write) -> RuntimeResult<()> {
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
                return Err(RuntimeError::LoadError {
                    path: PathBuf::from(format!("<mock:{id}>")),
                    reason,
                });
            }

            // Write module bytes
            let bytes = self
                .modules
                .lock()
                .unwrap()
                .get(id)
                .cloned()
                .ok_or_else(|| RuntimeError::LoadError {
                    path: PathBuf::from(format!("<mock:{id}>")),
                    reason: "module not found in mock store".into(),
                })?;
            writer
                .write_all(&bytes)
                .map_err(|e| RuntimeError::LoadError {
                    path: PathBuf::from(format!("<mock:{id}>")),
                    reason: e.to_string(),
                })
        }
    }
}
