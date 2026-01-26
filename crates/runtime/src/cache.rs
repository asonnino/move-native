//! Module and function cache for native Move modules
//!
//! Caches function pointers to avoid repeated disk I/O and dlsym calls.
//! Uses moka's concurrent cache for thread-safe access without requiring
//! mutable references.
//!
//! TODO: Currently loads from filesystem. In production, this should
//! read native module bytes from the blockchain state database (e.g., RocksDB)
//! and load via memfd to keep state consistent with the chain.

use std::{
    path::{Path, PathBuf},
    sync::Arc,
};

use moka::sync::Cache;

use crate::{
    error::RuntimeResult,
    module::{FunctionHandle, NativeModule},
};

/// Identifier for a native module
///
/// TODO: Replace with actual module ID type (e.g., Move ModuleId)
#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Debug))]
pub struct ModuleId(PathBuf);

impl ModuleId {
    /// Create a new module ID from a path
    pub fn new(path: impl AsRef<Path>) -> Self {
        Self(path.as_ref().to_path_buf())
    }

    /// Get the underlying path
    #[cfg(test)]
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
/// Generic over `F`, the function pointer type. All cached functions
/// must have the same signature (uniform ABI).
///
/// This cache is thread-safe and can be shared across threads via `Arc<ModuleCache>`.
/// All methods take `&self` rather than `&mut self`.
///
/// # Type Parameters
///
/// * `F` - The function pointer type (e.g., `unsafe extern "C" fn(*mut Context)`)
///
/// # Example
///
/// ```no_run
/// use runtime::ModuleCache;
///
/// // Define your function type (typically in the compiler crate)
/// type MoveFn = unsafe extern "C" fn();
///
/// // Create a typed cache with capacity for 128 modules and 1024 functions
/// let cache: ModuleCache<MoveFn> = ModuleCache::new(128, 1024);
///
/// // Get a function (loads module on first access, caches both)
/// let function_handler = unsafe { cache.get_or_load("module.dylib", "my_func")? };
/// // The module stays loaded as long as function_handler is alive
/// let ptr = function_handler.ptr();
/// # Ok::<(), runtime::RuntimeError>(())
/// ```
///
/// # Lifetime Management
///
/// Both the module cache and function cache use moka's LRU eviction.
/// Modules are cached independently from functions, allowing the same
/// module to serve multiple function lookups efficiently.
///
/// TODO: In production, the backing storage should be the blockchain
/// state database rather than the filesystem. Native module bytes would
/// be stored in RocksDB keyed by module ID, and loaded via memfd_create
/// to maintain consistency with on-chain state.
pub struct ModuleCache<F: Copy + Send + Sync + 'static> {
    /// Cache of loaded modules - keyed by ModuleId
    modules: Cache<ModuleId, Arc<NativeModule>>,
    /// Cache of function handles - keyed by FunctionId
    functions: Cache<FunctionId, FunctionHandle<F>>,
}

impl<F: Copy + Send + Sync + 'static> ModuleCache<F> {
    /// Create a new cache with the specified capacity limits
    ///
    /// # Arguments
    ///
    /// * `module_capacity` - Maximum number of modules to cache
    /// * `function_capacity` - Maximum number of functions to cache
    pub fn new(module_capacity: u64, function_capacity: u64) -> Self {
        Self {
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
    /// This method is thread-safe and uses `&self` rather than `&mut self`.
    /// Concurrent calls for the same module/function will be deduplicated.
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
        module_path: impl AsRef<Path>,
        function_name: &str,
    ) -> RuntimeResult<FunctionHandle<F>> {
        let path = module_path.as_ref();
        let module_id = ModuleId::new(path);
        let function_id = FunctionId::new(module_id.clone(), function_name);

        // Fast path: function already cached
        if let Some(handle) = self.functions.get(&function_id) {
            return Ok(handle);
        }

        // Load module (fast path avoids try_get_with coordination overhead)
        let module = if let Some(m) = self.modules.get(&module_id) {
            m
        } else {
            self.modules
                .try_get_with(module_id, || NativeModule::load(path))
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

    use crate::{ModuleCache, ModuleId};

    // Test function type for unit tests
    type TestFn = unsafe extern "C" fn();

    #[test]
    fn test_new_cache_is_empty() {
        let cache: ModuleCache<TestFn> = ModuleCache::new(128, 128);
        assert!(cache.is_empty());
    }

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

    #[test]
    fn test_get_or_load_nonexistent_module_returns_error() {
        let cache: ModuleCache<TestFn> = ModuleCache::new(128, 128);
        let result = unsafe { cache.get_or_load("/nonexistent/module.dylib", "func") };
        assert!(result.is_err());
        assert!(cache.is_empty());
    }
}
