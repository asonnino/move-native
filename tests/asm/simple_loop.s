// simple_loop.s - Simple loop for testing gas instrumentation
// This is a basic Arm64 assembly file with a loop that needs gas metering

// macOS Mach-O binaries use underscore prefix for C symbols (_simple_loop),
// while Linux ELF binaries use the name directly (simple_loop).
// Define both so the same assembly works on both platforms.
.global _simple_loop
.global simple_loop
.align 4

_simple_loop:
simple_loop:
    mov x0, #0              // counter = 0
    mov x1, #1000           // limit (use smaller value for valid immediate)

.Lloop:
    add x0, x0, #1          // counter++
    cmp x0, x1
    b.lt .Lloop             // back-edge: needs gas check

    ret
