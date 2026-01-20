// test_loop.s - Simple loop for testing gas instrumentation
// This is a basic Arm64 assembly file with a loop that needs gas metering

// macOS Mach-O binaries use underscore prefix for C symbols (_test_loop),
// while Linux ELF binaries use the name directly (test_loop).
// Define both so the same assembly works on both platforms.
.global _test_loop
.global test_loop
.align 4

_test_loop:
test_loop:
    mov x0, #0              // counter = 0
    mov x1, #1000           // limit (use smaller value for valid immediate)

.Lloop:
    add x0, x0, #1          // counter++
    cmp x0, x1
    b.lt .Lloop             // back-edge: needs gas check

    ret
