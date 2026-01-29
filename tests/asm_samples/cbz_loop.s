// cbz_loop.s - Loop using cbnz for back-edge
// Tests that cbz/cbnz branches are correctly identified as back-edges.

.global _cbz_loop
.global cbz_loop
.align 4

_cbz_loop:
cbz_loop:
    mov x0, #10             // counter = 10

.Lloop:
    sub x0, x0, #1          // counter--
    cbnz x0, .Lloop         // back-edge using cbnz (branch if not zero)

    ret
