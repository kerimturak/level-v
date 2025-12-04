/* ============================================================
 * Ceres-V Startup Code for Embench Benchmarks
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
    
    /* Copy data section if needed (from ROM to RAM) */
    la      t0, _data_lma      /* Load address */
    la      t1, _data_start    /* Virtual address */
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
    
    /* Enable cycle/instret counters access */
    li      t0, -1
    csrw    mcounteren, t0
    
    /* Initialize performance counters */
    csrw    mcycle, zero
    csrw    minstret, zero
    
    /* Call main (argc=0, argv=NULL) */
    li      a0, 0
    li      a1, 0
    call    main
    
    /* Exit - call _exit with return value */
    call    _exit
    
    /* Should not reach here */
    j       .

/* ============================================================
 * Trap Handler
 * ============================================================
 */
    .align 4
_trap_entry:
    /* Save minimal context */
    addi    sp, sp, -16
    sw      ra, 0(sp)
    sw      t0, 4(sp)
    sw      t1, 8(sp)
    sw      a0, 12(sp)
    
    /* Read cause */
    csrr    t0, mcause
    
    /* Check if interrupt (msb set) */
    bltz    t0, _handle_interrupt
    
    /* Exception handling */
    li      t1, 11                  /* Environment call from M-mode */
    beq     t0, t1, _handle_ecall
    
    /* Unknown exception - infinite loop */
    j       .

_handle_ecall:
    /* Handle system call if needed */
    /* For now, just return */
    csrr    t0, mepc
    addi    t0, t0, 4
    csrw    mepc, t0
    j       _trap_exit

_handle_interrupt:
    /* Clear interrupt cause */
    /* For now, just acknowledge */
    j       _trap_exit

_trap_exit:
    /* Restore context */
    lw      ra, 0(sp)
    lw      t0, 4(sp)
    lw      t1, 8(sp)
    lw      a0, 12(sp)
    addi    sp, sp, 16
    mret

/* ============================================================
 * Weak functions for C library
 * ============================================================
 */
    .weak   _init
    .weak   _fini
_init:
_fini:
    ret

    .section .data
    .align 4
