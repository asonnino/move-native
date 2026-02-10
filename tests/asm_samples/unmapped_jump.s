// unmapped_jump.s - Triggers SIGSEGV by jumping to unmapped address
// Used to test memory fault handling in the runtime
//
// Note: This uses an indirect branch (br x0) which the verifier would reject
// in production. For testing purposes, we skip verification.

// macOS Mach-O binaries use underscore prefix for C symbols,
// while Linux ELF binaries use the name directly.
// Define both so the same assembly works on both platforms.
.global _unmapped_jump
.global unmapped_jump
.align 4

_unmapped_jump:
unmapped_jump:
    mov x0, #0xDEAD
    lsl x0, x0, #32     // x0 = 0xDEAD00000000 (unmapped)
    br x0               // SIGSEGV: jump to unmapped address
