// nested_fault.s - Fault inside a nested bl call
// Tests that fault recovery works when LR has been clobbered by bl.
// With the old trampoline approach (ret), LR would point inside this
// function after bl, causing the trampoline to jump back into Move code
// instead of returning to the executor.

// macOS Mach-O binaries use underscore prefix for C symbols,
// while Linux ELF binaries use the name directly.
// Define both so the same assembly works on both platforms.
.global _nested_fault
.global nested_fault
.align 4

_nested_fault:
nested_fault:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    bl _helper_that_faults      // LR now points to ldp below, NOT executor
    ldp x29, x30, [sp], #16
    ret

_helper_that_faults:
helper_that_faults:
    mov x0, #0
    ldr x1, [x0]               // SIGSEGV: LR points inside nested_fault
    ret
