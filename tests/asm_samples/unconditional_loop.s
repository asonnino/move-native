// unconditional_loop.s - Loop with unconditional back-edge
// Tests that unconditional `b` branches are correctly instrumented.
// This is effectively a counted loop that exits via conditional forward branch.

.global _unconditional_loop
.global unconditional_loop
.align 4

_unconditional_loop:
unconditional_loop:
    mov x0, #0              // counter = 0
    mov x1, #100            // limit

.Lloop:
    add x0, x0, #1          // counter++
    cmp x0, x1
    b.ge .Ldone             // forward branch to exit
    b .Lloop                // unconditional back-edge: needs gas check

.Ldone:
    ret
