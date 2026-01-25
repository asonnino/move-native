//! Dynamic library loading for native Move modules
//!
//! Provides a safe wrapper around libloading for loading compiled
//! Move modules and resolving function symbols.

use std::path::Path;

use libloading::{Library, Symbol as LibSymbol};

use crate::error::{RuntimeError, RuntimeResult};

/// A function symbol from a native module
///
/// This is a wrapper around the raw function pointer that provides
/// safe access to the function.
pub struct Symbol<F: 'static> {
    inner: LibSymbol<'static, F>,
}

impl<F: 'static> std::fmt::Debug for Symbol<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Symbol").finish_non_exhaustive()
    }
}

impl<F: 'static> std::ops::Deref for Symbol<F> {
    type Target = F;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

/// A loaded native module
///
/// Wraps a dynamically loaded library (.dylib on macOS, .so on Linux)
/// and provides safe access to exported functions.
pub struct NativeModule {
    library: Library,
}

impl std::fmt::Debug for NativeModule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NativeModule").finish_non_exhaustive()
    }
}

impl NativeModule {
    /// Load a native module from the specified path
    pub fn load<P: AsRef<Path>>(path: P) -> RuntimeResult<Self> {
        let path = path.as_ref();
        // Safety: The library is loaded with default flags.
        // The caller must ensure the library is safe to load.
        let library = unsafe { Library::new(path) }.map_err(|e| RuntimeError::LoadError {
            path: path.to_path_buf(),
            reason: e.to_string(),
        })?;

        Ok(Self { library })
    }

    /// Get a function symbol from the module
    ///
    /// # Type Parameters
    ///
    /// * `F` - The function signature type (e.g., `unsafe extern "C" fn()`)
    ///
    /// # Arguments
    ///
    /// * `name` - The symbol name to look up
    ///
    /// # Errors
    ///
    /// Returns `RuntimeError::SymbolNotFound` if the symbol doesn't exist.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - The type parameter `F` matches the actual function signature
    /// - The function is safe to call (e.g., properly instrumented)
    ///
    /// # Example
    ///
    /// ```no_run
    /// use runtime::NativeModule;
    ///
    /// let module = NativeModule::load("my_module.dylib")?;
    /// let func = unsafe { module.get_function::<unsafe extern "C" fn()>("my_function")? };
    /// # Ok::<(), runtime::RuntimeError>(())
    /// ```
    pub unsafe fn get_function<F: 'static>(&self, name: &str) -> RuntimeResult<Symbol<F>> {
        // Note: dlsym handles platform symbol conventions automatically.
        // On macOS, dlsym("foo") finds "_foo" in Mach-O binaries.
        // On Linux, dlsym("foo") finds "foo" in ELF binaries.
        let symbol: LibSymbol<F> =
            self.library
                .get(name.as_bytes())
                .map_err(|_| RuntimeError::SymbolNotFound {
                    symbol: name.to_string(),
                })?;

        Ok(Symbol {
            // Leak the symbol to get a 'static lifetime
            // This is safe because the Library outlives the Symbol usage
            inner: std::mem::transmute(symbol),
        })
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::{NativeModule, RuntimeError};

    #[test]
    fn test_load_nonexistent() {
        let result = NativeModule::load("/nonexistent/path/to/library.dylib");
        assert!(result.is_err());
        match result.unwrap_err() {
            RuntimeError::LoadError { path, .. } => {
                assert_eq!(
                    path,
                    Path::new("/nonexistent/path/to/library.dylib").to_path_buf()
                );
            }
            _ => panic!("expected LoadError"),
        }
    }
}
