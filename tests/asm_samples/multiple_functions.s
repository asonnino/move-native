// multiple_functions.s - Multiple entry points in one file
// Tests symbol resolution for different functions in the same module.

.global _func_add
.global func_add
.global _func_mul
.global func_mul
.align 4

// First function: simple addition loop
// Adds numbers from 1 to 100, returns sum in x0
_func_add:
func_add:
    mov x0, #0              // sum = 0
    mov x1, #100            // limit (fixed, not input)
    mov x2, #0              // i = 0

.Ladd_loop:
    add x2, x2, #1          // i++
    add x0, x0, x2          // sum += i
    cmp x2, x1
    b.lt .Ladd_loop         // back-edge

    ret

// Second function: simple multiplication via repeated addition
// Multiplies 5 * 20, returns product in x0
_func_mul:
func_mul:
    mov x0, #0              // product = 0
    mov x1, #5              // multiplicand
    mov x2, #20             // multiplier
    mov x3, #0              // counter = 0

.Lmul_loop:
    add x0, x0, x1          // product += x1
    add x3, x3, #1          // counter++
    cmp x3, x2
    b.lt .Lmul_loop         // back-edge

    ret
