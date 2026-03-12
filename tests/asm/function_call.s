// function_call.s - Loop containing a function call
// Tests that x23 (gas register) is preserved across bl calls since it's callee-saved.
// Note: Helper function is placed AFTER the main function so `bl _helper` is a
// forward branch (not a back-edge).

.global _loop_with_call
.global loop_with_call
.align 4

_loop_with_call:
loop_with_call:
    // Save link register (x30) since we'll use bl which overwrites it
    stp x29, x30, [sp, #-16]!
    mov x29, sp

    mov x0, #0              // accumulator = 0
    mov x9, #100            // limit

.Lloop:
    bl _helper              // call helper (forward branch, not back-edge)
    cmp x0, x9
    b.lt .Lloop             // back-edge: needs gas check

    // Restore link register and return
    ldp x29, x30, [sp], #16
    ret

// Helper function placed after main function
// This ensures bl _helper is a forward branch, not a back-edge
// Note: Helper is a leaf function (no calls), so doesn't need to save LR
_helper:
helper:
    add x0, x0, #1          // increment accumulator
    ret
