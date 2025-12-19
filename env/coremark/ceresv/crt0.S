/*
 * Startup code for Ceres-V RV32IMC_Zicsr processor
 * Simple baremetal startup without interrupts
 */

    .section .text.init
    .globl _start
    .type _start, @function

_start:
    /* Disable interrupts */
    csrw mie, zero
    csrw mip, zero
    
    /* Initialize all registers to zero */
    li x1, 0
    li x2, 0
    li x3, 0
    li x4, 0
    li x5, 0
    li x6, 0
    li x7, 0
    li x8, 0
    li x9, 0
    li x10, 0
    li x11, 0
    li x12, 0
    li x13, 0
    li x14, 0
    li x15, 0
    li x16, 0
    li x17, 0
    li x18, 0
    li x19, 0
    li x20, 0
    li x21, 0
    li x22, 0
    li x23, 0
    li x24, 0
    li x25, 0
    li x26, 0
    li x27, 0
    li x28, 0
    li x29, 0
    li x30, 0
    li x31, 0

    /* Initialize global pointer */
.option push
.option norelax
    la gp, __global_pointer$
.option pop

    /* Initialize stack pointer */
    la sp, _stack_top

    /* Note: .data section is already in place (baremetal, no relocation needed) */

    /* Clear BSS section */
    la t0, _bss_start
    la t1, _bss_end
bss_clear:
    bge t0, t1, bss_done
    sw zero, 0(t0)
    addi t0, t0, 4
    j bss_clear
bss_done:

    /* Call main function */
    li a0, 0        /* argc = 0 */
    li a1, 0        /* argv = NULL */
    call main

    /* If main returns, loop forever */
_exit:
    j _exit

    .size _start, . - _start

/* Provide weak symbols for BSS and stack if not defined by linker */
    .weak _bss_start
    .weak _bss_end
    .weak _stack_top
    .weak __global_pointer$
