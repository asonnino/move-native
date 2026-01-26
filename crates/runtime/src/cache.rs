//! Module and function cache for native Move modules
//!
//! Caches function pointers to avoid repeated store I/O and dlsym calls.
//! Uses moka's concurrent cache for thread-safe access without requiring
//! mutable references.
//!
//! The cache is generic over a `ModuleStore` trait, allowing different
//! backing stores (filesystem, database, in-memory for testing).

use std::{hash::Hash, sync::Arc};

use moka::sync::Cache;

use crate::{
    error::RuntimeResult,
    module::{FunctionHandle, NativeModule},
    store::ModuleStore,
};

/// Key for function cache: (module_id, function_name)
#[derive(Clone, PartialEq, Eq, Hash)]
struct FunctionId<Id> {
    module: Id,
    name: String,
}

impl<Id: Clone> FunctionId<Id> {
    /// Create a new function ID
    fn new(module: Id, name: &str) -> Self {
        Self {
            module,
            name: name.to_string(),
        }
    }
}

/// Cache for loaded native modules and function lookups
///
/// Generic over:
/// - `S` - The module store (where bytes come from)
/// - `F` - The function pointer type (uniform ABI)
///
/// This cache is thread-safe and can be shared across threads via `Arc<ModuleCache>`.
/// All methods take `&self` rather than `&mut self`.
///
/// # Example
///
/// ```no_run
/// use std::path::PathBuf;
/// use runtime::{ModuleCache, FileSystemStore};
///
/// // Define your function type (typically in the compiler crate)
/// type MoveFn = unsafe extern "C" fn();
///
/// // Create a cache with filesystem backing
/// let store = FileSystemStore::new();
/// let cache: ModuleCache<FileSystemStore, MoveFn> = ModuleCache::new(store, 128);
///
/// // Get a function (loads module on first access, caches both)
/// let module_id = PathBuf::from("module.dylib");
/// let function_handler = unsafe { cache.get_or_load(&module_id, "my_func")? };
/// let ptr = function_handler.ptr();
/// # Ok::<(), runtime::RuntimeError>(())
/// ```
///
/// # Lifetime Management
///
/// Both the module cache and function cache use moka's LRU eviction.
/// Modules are cached independently from functions, allowing the same
/// module to serve multiple function lookups efficiently.
pub struct ModuleCache<S: ModuleStore, F: Copy + Send + Sync + 'static> {
    /// The backing store for loading module bytes
    store: S,
    /// Cache of loaded modules - keyed by store's Id type
    modules: Cache<S::Id, Arc<NativeModule>>,
    /// Cache of function handles - keyed by (module_id, function_name)
    functions: Cache<FunctionId<S::Id>, FunctionHandle<F>>,
}

impl<S: ModuleStore, F> ModuleCache<S, F>
where
    S::Id: Hash,
    F: Copy + Send + Sync + 'static,
{
    /// Create a new cache with the specified store and capacity
    ///
    /// # Arguments
    ///
    /// * `store` - The backing store for loading module bytes
    /// * `capacity` - Maximum number of entries in each cache (modules and functions)
    pub fn new(store: S, capacity: u64) -> Self {
        Self {
            store,
            modules: Cache::builder().max_capacity(capacity).build(),
            functions: Cache::builder().max_capacity(capacity).build(),
        }
    }

    /// Get or load a function from a module
    ///
    /// Returns a `FunctionHandle` that holds both the function pointer and
    /// a reference to the module. The module stays loaded as long as the
    /// returned `FunctionHandle` (or any clone of it) is alive.
    ///
    /// # Safety
    ///
    /// The caller must ensure the type parameter `F` matches the actual
    /// function signature in the library.
    ///
    /// # Errors
    ///
    /// Returns `RuntimeError::LoadError` if the module cannot be loaded,
    /// or `RuntimeError::SymbolNotFound` if the function doesn't exist.
    pub unsafe fn get_or_load(
        &self,
        module_id: &S::Id,
        function_name: &str,
    ) -> RuntimeResult<FunctionHandle<F>> {
        let function_id = FunctionId::new(module_id.clone(), function_name);

        // Fast path: function already cached
        if let Some(handle) = self.functions.get(&function_id) {
            return Ok(handle);
        }

        // Load module (fast path avoids try_get_with coordination overhead)
        let module = if let Some(m) = self.modules.get(module_id) {
            m
        } else {
            self.modules
                .try_get_with(module_id.clone(), || {
                    let bytes = self.store.load_bytes(module_id)?;
                    NativeModule::load_from_bytes(&bytes)
                })
                .map_err(Arc::unwrap_or_clone)?
        };

        // Cache function (deduplicated by FunctionId)
        self.functions
            .try_get_with(function_id, || module.get_function::<F>(function_name))
            .map_err(Arc::unwrap_or_clone)
    }
}
