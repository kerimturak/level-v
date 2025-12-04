/* ============================================================
 * Ceres-V Startup Code for Dhrystone
 * ============================================================
 */

    .section .text.init, "ax"
    .global _start
    .global _trap_entry

_start:
    /* Disable interrupts */
    csrw    mie, zero
    
    /* Setup stack pointer */
    la      sp, _stack_top
    
    /* Setup global pointer */
    .option push
    .option norelax
    la      gp, __global_pointer$
    .option pop
    
    /* Clear BSS section */
    la      t0, _bss_start
    la      t1, _bss_end
1:
    bge     t0, t1, 2f
    sw      zero, 0(t0)
    addi    t0, t0, 4
    j       1b
2:
    
    /* Copy data section if needed */
    la      t0, _data_lma
    la      t1, _data_start
    la      t2, _data_end
3:
    bge     t1, t2, 4f
    lw      t3, 0(t0)
    sw      t3, 0(t1)
    addi    t0, t0, 4
    addi    t1, t1, 4
    j       3b
4:
    
    /* Setup trap handler */
    la      t0, _trap_entry
    csrw    mtvec, t0
    
    /* Initialize counters */
    csrw    mcycle, zero
    csrw    minstret, zero
    
    /* Call main */
    li      a0, 0
    li      a1, 0
    call    main
    
    /* Exit */
    call    _exit
    j       .

/* Trap Handler */
    .align 4
_trap_entry:
    csrr    t0, mcause
    csrr    t0, mepc
    addi    t0, t0, 4
    csrw    mepc, t0
    mret

    .weak   _init
    .weak   _fini
_init:
_fini:
    ret
