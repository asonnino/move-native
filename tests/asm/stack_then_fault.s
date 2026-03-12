// stack_then_fault.s - Modifies stack then faults
// Tests that SP restoration works even when the faulting code
// has modified the stack before the fault

// macOS Mach-O binaries use underscore prefix for C symbols,
// while Linux ELF binaries use the name directly.
// Define both so the same assembly works on both platforms.
.global _stack_then_fault
.global stack_then_fault
.align 4

_stack_then_fault:
stack_then_fault:
    stp x29, x30, [sp, #-16]!   // Push frame (modifies SP)
    mov x29, sp
    sub sp, sp, #32             // Allocate local space
    mov x0, #0
    ldr x1, [x0]                // FAULT with corrupted stack
    add sp, sp, #32
    ldp x29, x30, [sp], #16
    ret
