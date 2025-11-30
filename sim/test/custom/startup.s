.section .text._start
.globl _start

_start:
    /* Set stack pointer */
    la sp, __stack_end
    
    /* Jump to main */
    jal ra, main
    
    /* Infinite loop on return */
    j _start

.section .bss
.align 4
__stack_start:
    .space 0x4000
__stack_end:
