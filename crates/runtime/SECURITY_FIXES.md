# Security Fixes Plan

Based on the security audit, here are the issues to address (excluding #7 secondary timeout).

---

## Phase 1: Quick Fixes (Trivial)

### Fix #5: Missing Signal Mask Configuration
**File:** `signal.rs:74-96`
**Risk:** Medium
**Effort:** Trivial

**Problem:** Handler installed without configuring `sa_mask`, allowing signals to interrupt during ucontext modification.

**Fix:**
```rust
// In install_inner(), before sigaction call:
libc::sigemptyset(&mut sa.sa_mask);
// Optionally block SIGTRAP during handler execution to prevent reentrancy:
// libc::sigaddset(&mut sa.sa_mask, SIGTRAP);
```

---

### Fix #6: Integer Overflow in Gas Calculation
**File:** `execute.rs:82-89`
**Risk:** Medium
**Effort:** Trivial

**Problem:** `gas_limit` cast from `u64` to `i64` silently wraps if `gas_limit > i64::MAX`.

**Fix Options:**
1. **Assert:** `assert!(gas_limit <= i64::MAX as u64)`
2. **Saturate:** `let gas_limit = gas_limit.min(i64::MAX as u64)`
3. **Return error:** Add `RuntimeError::GasLimitTooLarge`

Recommendation: Option 3 (return error) is cleanest for a library.

---

## Phase 2: Soundness Fix (Important)

### Fix #2: Symbol Lifetime Transmutation
**File:** `loader.rs:99-106`
**Risk:** High
**Effort:** Medium

**Problem:** `Symbol<F>` has `'static` lifetime via transmute, but can outlive `NativeModule`.

```rust
// Current (unsound):
pub struct Symbol<F: 'static> {
    inner: LibSymbol<'static, F>,
}

// NativeModule::get_function returns Symbol by value
// User can drop NativeModule while holding Symbol -> use-after-free
```

**Fix Options:**

**Option A: Tie lifetime to NativeModule**
```rust
pub struct Symbol<'a, F: 'static> {
    inner: LibSymbol<'a, F>,
}

impl NativeModule {
    pub unsafe fn get_function<'a, F>(&'a self, name: &str) -> RuntimeResult<Symbol<'a, F>>
}
```
- Pro: Correct by construction
- Con: Lifetime propagates to `ModuleCache`, making the API more complex

**Option B: Symbol holds Arc<NativeModule>**
```rust
pub struct Symbol<F: 'static> {
    _module: Arc<NativeModule>,  // prevents drop
    inner: LibSymbol<'static, F>,
}
```
- Pro: No lifetime parameters needed
- Con: Arc overhead, NativeModule needs to be wrapped in Arc

**Option C: Document and keep current design**
- The cache already stores `Arc<NativeModule>` alongside symbols
- Add `# Safety` docs that Symbol must not outlive its module
- Pro: No API changes
- Con: Unsound in general, relies on correct usage

**Recommendation:** Option A is cleanest. The cache can store `(Arc<NativeModule>, Symbol<'static, F>)` where the Arc keeps the module alive, and we transmute internally in the cache only.

---

## Phase 3: Signal Handler Improvements

### Fix #3: No Handler Chaining
**File:** `signal.rs:74-96`
**Risk:** High (silent failure)
**Effort:** Medium

**Problem:** Previous SIGTRAP handler is discarded. If something else installs a handler later, gas metering silently breaks.

**Fix:**
```rust
static PREVIOUS_HANDLER: OnceLock<sigaction> = OnceLock::new();

fn install_inner() -> RuntimeResult<()> {
    unsafe {
        let mut sa: sigaction = std::mem::zeroed();
        let mut old_sa: sigaction = std::mem::zeroed();

        sa.sa_sigaction = Self::handle_sigtrap as usize;
        sa.sa_flags = SA_SIGINFO;
        libc::sigemptyset(&mut sa.sa_mask);

        if sigaction(SIGTRAP, &sa, &mut old_sa) != 0 {
            return Err(...);
        }

        // Save previous handler for chaining
        let _ = PREVIOUS_HANDLER.set(old_sa);
    }
    Ok(())
}

extern "C" fn handle_sigtrap(sig: c_int, info: *mut siginfo_t, ctx: *mut c_void) {
    // Check if this is our brk #0 (could inspect info->si_code or instruction at PC)
    // For now, assume all SIGTRAP in our code is from brk #0

    OUT_OF_GAS.with(|flag| flag.set(true));
    unsafe { Self::advance_pc(ctx); }

    // Optionally chain to previous handler for non-brk SIGTRAPs
    // (complex: need to detect if this was brk #0 or something else)
}
```

**Consideration:** Detecting brk #0 vs other SIGTRAP sources (breakpoints, ptrace) requires reading the instruction at PC. May not be worth the complexity for a controlled environment.

**Simpler alternative:** Verify handler is still installed before each `execute()`:
```rust
pub unsafe fn execute<F: Copy>(&self, entry: F, gas_limit: u64) -> RuntimeResult<GasResult> {
    self.handler.verify_installed()?;  // Check sigaction returns our handler
    // ...
}
```

---

### Fix #1: Async-Signal-Safety Violation
**File:** `signal.rs:103-109`
**Risk:** Critical (theoretical)
**Effort:** High

**Problem:** `thread_local!` access in signal handler is not guaranteed async-signal-safe.

**Current code:**
```rust
extern "C" fn handle_sigtrap(...) {
    OUT_OF_GAS.with(|flag| flag.set(true));  // TLS access
    unsafe { Self::advance_pc(ctx); }
}
```

**Analysis:**
- We use `const { Cell::new(false) }` so no lazy initialization
- On aarch64, TLS is typically accessed via TPIDR_EL0 register + offset
- In practice, this is safe on our target platforms

**Fix Options:**

**Option A: Use a reserved register for the flag**
Reserve x22 (callee-saved) for out-of-gas flag pointer:
```rust
// In execute_with_gas:
// 1. Store address of thread-local flag in x22 before call
// 2. Signal handler reads x22 to find flag location
// 3. Writes directly to that address (no TLS lookup)

extern "C" fn handle_sigtrap(..., ctx: *mut c_void) {
    unsafe {
        let uctx = ctx as *mut libc::ucontext_t;
        // Read x22 from context (contains &Cell<bool>)
        let flag_ptr = /* extract x22 from mcontext */;
        *(flag_ptr as *mut bool) = true;
        Self::advance_pc(ctx);
    }
}
```
- Pro: Completely async-signal-safe
- Con: Uses another register, complex setup

**Option B: Use sig_atomic_t / AtomicBool with thread ID**
```rust
// Global array indexed by small thread ID
static OUT_OF_GAS_FLAGS: [AtomicBool; MAX_THREADS] = ...;

// Store thread index in x22, handler indexes into array
```
- Con: Requires thread ID management, MAX_THREADS limit

**Option C: Accept current design with documentation**
- Document that we rely on platform-specific TLS behavior
- Add compile-time assertions for supported platforms
- Monitor for issues

**Recommendation:** Start with Option C for development. Implement Option A for production if needed.

---

## Phase 4: Verifier Issue (Track Separately)

### Fix #4: Gas Counter Save/Restore Detection
**File:** `native-verifier` crate (not runtime)
**Risk:** Medium
**Effort:** Medium

**Problem:** Malicious code could save x23 to stack, do work, restore x23 to bypass metering.

**Fix:** The verifier must reject:
- `str x23, [...]` - store x23 to memory
- `stp x23, xN, [...]` - store pair including x23
- `stp xN, x23, [...]` - store pair including x23

**Note:** This is a verifier issue, not a runtime issue. Track in native-verifier backlog.

---

## Phase 5: Low Priority

### Fix #8: Cache Size Limits
**File:** `cache.rs`
**Risk:** Low
**Effort:** Medium

Add LRU eviction or size limits. Not urgent until we have many modules.

---

### Fix #9: Path Sanitization in Errors
**File:** `error.rs`
**Risk:** Low
**Effort:** Low

Sanitize file paths in production builds. Use `#[cfg(debug_assertions)]` for full paths.

---

### Fix #10: Document PC Advancement Assumption
**File:** `signal.rs:128`
**Risk:** Low
**Effort:** Trivial

Add comment that ARM64 has fixed 4-byte instructions, making `+= 4` correct.

---

## Execution Order

1. **Phase 1:** Fix #5, #6 (trivial, do together)
2. **Phase 2:** Fix #2 (important soundness fix)
3. **Phase 3:** Fix #3 (handler verification), then #1 if needed
4. **Phase 4:** Track #4 for verifier
5. **Phase 5:** #8, #9, #10 as time permits
