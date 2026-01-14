// test_loop.s - Simple loop for testing gas instrumentation
// This is a basic Arm64 assembly file with a loop that needs gas metering

.global _test_loop
.align 4

_test_loop:
    mov x0, #0              // counter = 0
    mov x1, #1000           // limit (use smaller value for valid immediate)

.Lloop:
    add x0, x0, #1          // counter++
    cmp x0, x1
    b.lt .Lloop             // back-edge: needs gas check

    ret
