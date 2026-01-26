//! Module and function cache for native Move modules
//!
//! Caches function pointers to avoid repeated disk I/O and dlsym calls.
//! The function cache uses LRU eviction and holds strong references to
//! modules, keeping them loaded as long as their functions are cached.
//!
//! TODO: Currently loads from filesystem. In production, this should
//! read native module bytes from the blockchain state database (e.g., RocksDB)
//! and load via memfd to keep state consistent with the chain.

use std::{
    collections::HashMap,
    marker::PhantomData,
    num::NonZeroUsize,
    path::{Path, PathBuf},
    sync::{Arc, Weak},
};

use lru::LruCache;

use crate::{error::RuntimeResult, loader::NativeModule};

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

/// A cached function pointer with its module reference
///
/// This wrapper ensures the module stays loaded as long as the function
/// pointer is held. When this struct is dropped, the module reference
/// is released (though the module may remain loaded if other references
/// exist in the cache or elsewhere).
///
/// # Type Parameters
///
/// * `F` - The function pointer type (e.g., `unsafe extern "C" fn()`)
pub struct FunctionHandle<F: Copy> {
    ptr: F,
    _module: Arc<NativeModule>,
}

impl<F: Copy> FunctionHandle<F> {
    /// Get the raw function pointer
    ///
    /// The pointer remains valid as long as this `FunctionHandle` is alive.
    pub fn ptr(&self) -> F {
        self.ptr
    }
}

impl<F: Copy> Clone for FunctionHandle<F> {
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr,
            _module: Arc::clone(&self._module),
        }
    }
}

impl<F: Copy + std::fmt::Debug> std::fmt::Debug for FunctionHandle<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FunctionHandle")
            .field("ptr", &self.ptr)
            .finish_non_exhaustive()
    }
}

/// Cache for loaded native modules and function lookups
///
/// Generic over `F`, the function pointer type. All cached functions
/// must have the same signature (uniform ABI).
///
/// # Type Parameters
///
/// * `F` - The function pointer type (e.g., `unsafe extern "C" fn(*mut Context)`)
///
/// # Example
///
/// ```no_run
/// use std::num::NonZeroUsize;
/// use runtime::ModuleCache;
///
/// // Define your function type (typically in the compiler crate)
/// type MoveFn = unsafe extern "C" fn();
///
/// // Create a typed cache with capacity for 128 functions
/// let capacity = NonZeroUsize::new(128).unwrap();
/// let mut cache: ModuleCache<MoveFn> = ModuleCache::new(capacity);
///
/// // Get a function (loads module on first access, caches both)
/// let cached_fn = unsafe { cache.get_or_load("module.dylib", "my_func")? };
/// // The module stays loaded as long as cached_fn is alive
/// let func_ptr = cached_fn.ptr();
/// # Ok::<(), runtime::RuntimeError>(())
/// ```
///
/// # Lifetime Management
///
/// The function cache holds `Arc<NativeModule>` references, keeping modules
/// loaded as long as any of their functions are cached. When a function is
/// evicted from the LRU cache, its `Arc` reference is dropped. When the last
/// function from a module is evicted, the module is unloaded.
///
/// TODO: In production, the backing storage should be the blockchain
/// state database rather than the filesystem. Native module bytes would
/// be stored in RocksDB keyed by module ID, and loaded via memfd_create
/// to maintain consistency with on-chain state.
pub struct ModuleCache<F: Copy + 'static> {
    /// Weak refs to modules - avoids reloading from disk when module still alive
    modules: HashMap<ModuleId, Weak<NativeModule>>,
    /// LRU cache of functions - holds strong refs that keep modules alive
    functions: LruCache<FunctionId, FunctionHandle<F>>,
    /// Marker for the function type
    _marker: PhantomData<F>,
}

impl<F: Copy + 'static> ModuleCache<F> {
    /// Create a new cache with the specified function capacity limit
    ///
    /// The capacity determines how many functions can be cached before
    /// LRU eviction kicks in. Modules are kept alive as long as any of
    /// their functions remain in the cache.
    ///
    /// # Arguments
    ///
    /// * `function_capacity` - Maximum number of functions to cache
    pub fn new(function_capacity: NonZeroUsize) -> Self {
        Self {
            // Worst case: each function from a different module
            modules: HashMap::with_capacity(function_capacity.get()),
            functions: LruCache::new(function_capacity),
            _marker: PhantomData,
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
        &mut self,
        module_path: impl AsRef<Path>,
        function_name: &str,
    ) -> RuntimeResult<FunctionHandle<F>> {
        let module_id = ModuleId::new(module_path.as_ref());
        let function_id = FunctionId::new(module_id.clone(), function_name);

        // Check function cache first (updates LRU order)
        if let Some(cached) = self.functions.get(&function_id) {
            return Ok(cached.clone());
        }

        // Try to get module from weak ref, or load from disk
        let module = match self.modules.get(&module_id).and_then(Weak::upgrade) {
            Some(m) => m,
            None => {
                let m = Arc::new(NativeModule::load(module_path)?);
                self.modules.insert(module_id.clone(), Arc::downgrade(&m));
                m
            }
        };

        // Look up function and insert into cache with module reference
        let ptr = module.get_function::<F>(function_name)?;
        let cached = FunctionHandle {
            ptr,
            _module: module,
        };

        // Insert into cache; if an entry was evicted, check if its module can be cleaned up
        if let Some((evicted_id, evicted_fn)) = self.functions.push(function_id, cached.clone()) {
            // If this was the last strong ref to the module, remove the stale weak ref
            if Arc::strong_count(&evicted_fn._module) == 1 {
                self.modules.remove(&evicted_id.module);
            }
        }

        Ok(cached)
    }

    /// Check if the cache is empty
    #[cfg(test)]
    pub fn is_empty(&self) -> bool {
        self.functions.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use std::{num::NonZeroUsize, path::Path};

    use crate::{ModuleCache, ModuleId};

    // Test function type for unit tests
    type TestFn = unsafe extern "C" fn();

    fn test_capacity() -> NonZeroUsize {
        NonZeroUsize::new(128).unwrap()
    }

    #[test]
    fn test_new_cache_is_empty() {
        let cache: ModuleCache<TestFn> = ModuleCache::new(test_capacity());
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
        let mut cache: ModuleCache<TestFn> = ModuleCache::new(test_capacity());
        let result = unsafe { cache.get_or_load("/nonexistent/module.dylib", "func") };
        assert!(result.is_err());
        assert!(cache.is_empty());
    }
}
