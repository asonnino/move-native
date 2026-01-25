//! Module and function cache for native Move modules
//!
//! Caches both loaded modules and function lookups to avoid repeated
//! disk I/O and dlsym calls.
//!
//! TODO: Currently loads from filesystem. In production, this should
//! read native module bytes from the blockchain state database (e.g., RocksDB)
//! and load via memfd to keep state consistent with the chain.

use std::{
    collections::HashMap,
    marker::PhantomData,
    path::{Path, PathBuf},
    sync::Arc,
};

use crate::{
    error::RuntimeResult,
    loader::{NativeModule, Symbol},
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
    pub fn new(module: ModuleId, name: &str) -> Self {
        Self {
            module,
            name: name.to_string(),
        }
    }
}

/// Cache for loaded native modules and function lookups
///
/// Generic over `F`, the function signature type. All cached functions
/// must have the same signature (uniform ABI).
///
/// Caches both modules (to avoid repeated dlopen) and function pointers
/// (to avoid repeated dlsym).
///
/// # Type Parameters
///
/// * `F` - The function signature type (e.g., `unsafe extern "C" fn(*mut Context)`)
///
/// # Example
///
/// ```ignore
/// // Define your function type (typically in the compiler crate)
/// type MoveFn = unsafe extern "C" fn(*mut Context);
///
/// // Create a typed cache
/// let mut cache: ModuleCache<MoveFn> = ModuleCache::new();
///
/// // Get a function (loads module on first access, caches both)
/// let func = unsafe { cache.get_or_load("module.dylib", "my_func")? };
/// ```
///
/// TODO: In production, the backing storage should be the blockchain
/// state database rather than the filesystem. Native module bytes would
/// be stored in RocksDB keyed by module ID, and loaded via memfd_create
/// to maintain consistency with on-chain state.
pub struct ModuleCache<F: 'static> {
    /// In-memory cache of loaded modules
    modules: HashMap<ModuleId, Arc<NativeModule>>,
    /// In-memory cache of function symbols
    functions: HashMap<FunctionId, Symbol<F>>,
    /// Marker for the function type
    _marker: PhantomData<F>,
}

impl<F: 'static> Default for ModuleCache<F> {
    fn default() -> Self {
        Self::new()
    }
}

impl<F: 'static> ModuleCache<F> {
    /// Create a new empty cache
    pub fn new() -> Self {
        Self {
            modules: HashMap::new(),
            functions: HashMap::new(),
            _marker: PhantomData,
        }
    }

    /// Get or load a function from a module
    ///
    /// Loads the module if not already cached, then looks up the function
    /// symbol if not already cached. Both are cached for future calls.
    ///
    /// # Arguments
    ///
    /// * `module_path` - Path to the shared library (.dylib on macOS, .so on Linux)
    /// * `function_name` - Name of the function symbol to look up
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
    ) -> RuntimeResult<&Symbol<F>> {
        let module_id = ModuleId::new(module_path.as_ref());
        let function_id = FunctionId::new(module_id.clone(), function_name);

        // Fast path: function already cached
        if self.functions.contains_key(&function_id) {
            return Ok(self.functions.get(&function_id).unwrap());
        }

        // Load module if not cached
        if !self.modules.contains_key(&module_id) {
            let module = Arc::new(NativeModule::load(module_path)?);
            self.modules.insert(module_id.clone(), module);
        }

        // Look up function and cache it
        let module = self.modules.get(&module_id).unwrap();
        let symbol = module.get_function::<F>(function_name)?;
        self.functions.insert(function_id.clone(), symbol);

        Ok(self.functions.get(&function_id).unwrap())
    }

    /// Check if the cache is empty
    #[cfg(test)]
    pub fn is_empty(&self) -> bool {
        self.modules.is_empty() && self.functions.is_empty()
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
        let cache: ModuleCache<TestFn> = ModuleCache::new();
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
        let mut cache: ModuleCache<TestFn> = ModuleCache::new();
        let result = unsafe { cache.get_or_load("/nonexistent/module.dylib", "func") };
        assert!(result.is_err());
        // Cache should remain empty on failure
        assert!(cache.is_empty());
    }

    #[test]
    fn test_default_creates_empty_cache() {
        let cache: ModuleCache<TestFn> = ModuleCache::default();
        assert!(cache.is_empty());
    }
}
