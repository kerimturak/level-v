/*
 * Minimal startup code for RISC-V CoreMark
 * Sets up stack and jumps to main
 */

.section .text.start
.global _start

_start:
    /* Initialize stack pointer */
    la sp, __stack_top

    /* Clear BSS section */
    la t0, __bss_start
    la t1, __bss_end
1:
    bge t0, t1, 2f
    sw zero, 0(t0)
    addi t0, t0, 4
    j 1b
2:

    /* Call main */
    call main

    /* Infinite loop after main returns */
3:
    j 3b
