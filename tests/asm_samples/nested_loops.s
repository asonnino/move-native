// nested_loops.s - Nested loop pattern for testing gas instrumentation
// Both inner and outer loops should receive gas checks at their back-edges.

.global _nested_loops
.align 4

_nested_loops:
    mov x0, #0              // outer counter = 0
    mov x2, #10             // outer limit

.Louter:
    mov x1, #0              // inner counter = 0
    mov x3, #10             // inner limit

.Linner:
    add x1, x1, #1          // inner counter++
    cmp x1, x3
    b.lt .Linner            // inner back-edge: needs gas check

    add x0, x0, #1          // outer counter++
    cmp x0, x2
    b.lt .Louter            // outer back-edge: needs gas check

    ret
