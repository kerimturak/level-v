/* ============================================================
 * Ceres-V Startup for Torture Tests
 * ============================================================
 */

    .section .text.init, "ax"
    .global _start
    .global _trap_handler

_start:
    /* Disable interrupts */
    csrw    mie, zero
    
    /* Setup stack */
    la      sp, _stack_top
    
    /* Setup global pointer */
    .option push
    .option norelax
    la      gp, __global_pointer$
    .option pop
    
    /* Setup trap handler */
    la      t0, _trap_handler
    csrw    mtvec, t0
    
    /* Clear registers */
    li      x1, 0
    li      x2, 0
    li      x4, 0
    li      x5, 0
    li      x6, 0
    li      x7, 0
    li      x8, 0
    li      x9, 0
    li      x10, 0
    li      x11, 0
    li      x12, 0
    li      x13, 0
    li      x14, 0
    li      x15, 0
    li      x16, 0
    li      x17, 0
    li      x18, 0
    li      x19, 0
    li      x20, 0
    li      x21, 0
    li      x22, 0
    li      x23, 0
    li      x24, 0
    li      x25, 0
    li      x26, 0
    li      x27, 0
    li      x28, 0
    li      x29, 0
    li      x30, 0
    li      x31, 0
    
    /* Restore stack */
    la      sp, _stack_top
    
    /* Jump to test */
    j       test_start

/* Trap handler - any trap is a fail */
    .align 4
_trap_handler:
    /* Store failure indicator */
    li      t0, 0x1FFFFFFC
    li      t1, 2           /* Trap failure code */
    sw      t1, 0(t0)
1:  j       1b

/* Weak test_start - will be overridden by actual test */
    .weak   test_start
test_start:
    j       _pass

/* Pass/Fail handlers */
    .global _pass
    .global _fail

_pass:
    li      t0, 0x1FFFFFFC
    li      t1, 0
    sw      t1, 0(t0)
1:  j       1b

_fail:
    li      t0, 0x1FFFFFFC
    li      t1, 1
    sw      t1, 0(t0)
1:  j       1b
