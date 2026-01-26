//! Module and function cache for native Move modules
//!
//! Caches function pointers to avoid repeated store I/O and dlsym calls.
//! Uses moka's concurrent cache for thread-safe access without requiring
//! mutable references.
//!
//! The cache is generic over a `ModuleStore` trait, allowing different
//! backing stores (filesystem, database, in-memory for testing).

use std::{
    path::{Path, PathBuf},
    sync::Arc,
};

use moka::sync::Cache;

use crate::{
    error::RuntimeResult,
    module::{FunctionHandle, NativeModule},
    store::ModuleStore,
};

/// Identifier for a native module
///
/// Currently wraps a filesystem path. In production, this could be
/// extended to support other ID schemes (e.g., Move ModuleId).
#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Debug))]
pub struct ModuleId(PathBuf);

impl ModuleId {
    /// Create a new module ID from a path
    pub fn new(path: impl AsRef<Path>) -> Self {
        Self(path.as_ref().to_path_buf())
    }

    /// Get the underlying path
    pub fn path(&self) -> &Path {
        &self.0
    }
}

/// Key for function cache: (module_id, function_name)
#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Debug))]
struct FunctionId {
    module: ModuleId,
    name: String,
}

impl FunctionId {
    /// Create a new function ID
    fn new(module: ModuleId, name: &str) -> Self {
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
/// use runtime::{ModuleCache, ModuleId, FileSystemStore};
///
/// // Define your function type (typically in the compiler crate)
/// type MoveFn = unsafe extern "C" fn();
///
/// // Create a cache with filesystem backing
/// let store = FileSystemStore::new();
/// let cache: ModuleCache<FileSystemStore, MoveFn> = ModuleCache::new(store, 128, 1024);
///
/// // Get a function (loads module on first access, caches both)
/// let module_id = ModuleId::new("module.dylib");
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
    /// Cache of loaded modules - keyed by ModuleId
    modules: Cache<ModuleId, Arc<NativeModule>>,
    /// Cache of function handles - keyed by FunctionId
    functions: Cache<FunctionId, FunctionHandle<F>>,
}

impl<S: ModuleStore, F: Copy + Send + Sync + 'static> ModuleCache<S, F> {
    /// Create a new cache with the specified store and capacity limits
    ///
    /// # Arguments
    ///
    /// * `store` - The backing store for loading module bytes
    /// * `module_capacity` - Maximum number of modules to cache
    /// * `function_capacity` - Maximum number of functions to cache
    pub fn new(store: S, module_capacity: u64, function_capacity: u64) -> Self {
        Self {
            store,
            modules: Cache::builder().max_capacity(module_capacity).build(),
            functions: Cache::builder().max_capacity(function_capacity).build(),
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
        module_id: &ModuleId,
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
                    let bytes = &self.store.load_bytes(&module_id)?;
                    NativeModule::load_from_bytes(&bytes)
                })
                .map_err(Arc::unwrap_or_clone)?
        };

        // Cache function (deduplicated by FunctionId)
        self.functions
            .try_get_with(function_id, || module.get_function::<F>(function_name))
            .map_err(Arc::unwrap_or_clone)
    }

    /// Check if the cache is empty
    #[cfg(test)]
    pub fn is_empty(&self) -> bool {
        self.functions.entry_count() == 0
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::ModuleId;

    #[test]
    fn test_module_id_from_path() {
        let id = ModuleId::new("/path/to/module.dylib");
        assert_eq!(id.path(), Path::new("/path/to/module.dylib"));
    }

    #[test]
    fn test_module_id_equality() {
        let id1 = ModuleId::new("/path/to/module.dylib");
        let id2 = ModuleId::new("/path/to/module.dylib");
        let id3 = ModuleId::new("/other/path.dylib");

        assert_eq!(id1, id2);
        assert_ne!(id1, id3);
    }
}
