// null_deref.s - Triggers SIGSEGV by dereferencing null pointer
// Used to test memory fault handling in the runtime

// macOS Mach-O binaries use underscore prefix for C symbols (_null_deref),
// while Linux ELF binaries use the name directly (null_deref).
// Define both so the same assembly works on both platforms.
.global _null_deref
.global null_deref
.align 4

_null_deref:
null_deref:
    mov x0, #0          // null pointer
    ldr x1, [x0]        // SIGSEGV: load from address 0
    ret
