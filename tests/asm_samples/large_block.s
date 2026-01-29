// large_block.s - Loop with many instructions in the basic block
// Tests that gas decrement correctly counts all instructions.

.global _large_block
.global large_block
.align 4

_large_block:
large_block:
    mov x0, #0              // counter
    mov x1, #10             // limit

.Lloop:
    // Many instructions in the loop body (20 total including branch)
    add x0, x0, #1
    add x2, x0, x0
    add x3, x2, x0
    add x4, x3, x0
    add x5, x4, x0
    sub x2, x2, #1
    sub x3, x3, #1
    sub x4, x4, #1
    sub x5, x5, #1
    eor x2, x2, x3
    eor x3, x3, x4
    eor x4, x4, x5
    orr x2, x2, x3
    orr x3, x3, x4
    and x2, x2, x3
    and x3, x3, x4
    mov x6, x2
    mov x7, x3
    cmp x0, x1
    b.lt .Lloop             // back-edge: should charge 20 instructions

    ret
