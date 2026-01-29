// forward_only.s - Code with forward branches only (no loops)
// This should NOT receive any gas instrumentation since there are no back-edges.
// Forward-only code is bounded by code size and will terminate.

.global _forward_only
.global forward_only
.align 4

_forward_only:
forward_only:
    mov x0, #0              // result = 0
    cmp x1, #10             // compare input with 10
    b.lt .Lsmall            // if input < 10, branch forward

    // input >= 10 path
    add x0, x0, #100
    b .Ldone

.Lsmall:
    // input < 10 path
    add x0, x0, #1

.Ldone:
    ret
