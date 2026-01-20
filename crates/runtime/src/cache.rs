//! Module cache for native Move modules
//!
//! TODO: Currently loads from filesystem. In production, this should
//! read native module bytes from the blockchain state database (e.g., RocksDB)
//! and load via memfd to keep state consistent with the chain.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::error::RuntimeResult;
use crate::loader::NativeModule;

/// Identifier for a native module
///
/// TODO: Replace with actual module ID type (e.g., Move ModuleId)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

impl<P: AsRef<Path>> From<P> for ModuleId {
    fn from(path: P) -> Self {
        Self::new(path)
    }
}

/// Cache for loaded native modules
///
/// Keeps modules in memory once loaded to avoid repeated disk I/O.
///
/// TODO: In production, the backing storage should be the blockchain
/// state database rather than the filesystem. Native module bytes would
/// be stored in RocksDB keyed by module ID, and loaded via memfd_create
/// to maintain consistency with on-chain state.
pub struct ModuleCache {
    /// In-memory cache of loaded modules
    loaded: HashMap<ModuleId, Arc<NativeModule>>,
}

impl Default for ModuleCache {
    fn default() -> Self {
        Self::new()
    }
}

impl ModuleCache {
    /// Create a new empty module cache
    pub fn new() -> Self {
        Self {
            loaded: HashMap::new(),
        }
    }

    /// Get or load a module
    ///
    /// If the module is already cached, returns the cached version.
    /// Otherwise, loads the module from disk and caches it.
    ///
    /// # Arguments
    ///
    /// * `path` - Path to the shared library (.dylib on macOS, .so on Linux)
    ///
    /// # Errors
    ///
    /// Returns `RuntimeError::LoadError` if the module cannot be loaded.
    pub fn get_or_load(&mut self, path: impl AsRef<Path>) -> RuntimeResult<Arc<NativeModule>> {
        let id = ModuleId::from(path.as_ref());

        // Check in-memory cache first
        if let Some(module) = self.loaded.get(&id) {
            return Ok(Arc::clone(module));
        }

        // Cache miss: load from disk
        let module = Arc::new(NativeModule::load(path)?);
        self.loaded.insert(id, Arc::clone(&module));

        Ok(module)
    }

    /// Check if a module is cached
    pub fn contains(&self, path: impl AsRef<Path>) -> bool {
        let id = ModuleId::from(path.as_ref());
        self.loaded.contains_key(&id)
    }

    /// Clear all cached modules
    pub fn clear(&mut self) {
        self.loaded.clear();
    }

    /// Number of cached modules
    pub fn len(&self) -> usize {
        self.loaded.len()
    }

    /// Check if the cache is empty
    pub fn is_empty(&self) -> bool {
        self.loaded.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_cache_is_empty() {
        let cache = ModuleCache::new();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_module_id_from_path() {
        let id: ModuleId = "/path/to/module.dylib".into();
        assert_eq!(id.path(), Path::new("/path/to/module.dylib"));
    }

    #[test]
    fn test_module_id_equality() {
        let id1: ModuleId = "/path/to/module.dylib".into();
        let id2: ModuleId = "/path/to/module.dylib".into();
        let id3: ModuleId = "/other/path.dylib".into();

        assert_eq!(id1, id2);
        assert_ne!(id1, id3);
    }

    #[test]
    fn test_contains_returns_false_for_uncached() {
        let cache = ModuleCache::new();
        assert!(!cache.contains("/nonexistent/module.dylib"));
    }

    #[test]
    fn test_get_or_load_nonexistent_returns_error() {
        let mut cache = ModuleCache::new();
        let result = cache.get_or_load("/nonexistent/module.dylib");
        assert!(result.is_err());
        // Cache should not store failed loads
        assert!(!cache.contains("/nonexistent/module.dylib"));
    }

    #[test]
    fn test_clear_empties_cache() {
        let mut cache = ModuleCache::new();
        // Since we can't easily load a real module in tests,
        // we just verify clear works on an empty cache
        cache.clear();
        assert!(cache.is_empty());
    }

    #[test]
    fn test_default_creates_empty_cache() {
        let cache = ModuleCache::default();
        assert!(cache.is_empty());
    }
}
