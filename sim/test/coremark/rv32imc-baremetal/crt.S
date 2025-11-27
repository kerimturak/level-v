    .section .text.init
    .globl _start
    .align  2

_start:
    /* gp ayarı */
    .option push
    .option norelax
    la gp, __global_pointer__
    .option pop

    /* stack pointer */
    la sp, _stack_top

    /* .bss temizleme */
    la t0, __bss_start
    la t1, __bss_end
bss_loop:
    beq t0, t1, bss_done
    sw zero, 0(t0)
    addi t0, t0, 4
    j bss_loop
bss_done:

    /* _init (opsiyonel) */
    .weak _init
    la t0, _init
    beqz t0, call_main
    jalr t0

call_main:
    /* main() çağır */
    .weak main
    la t0, main
    beqz t0, hang
    jalr t0

hang:
    j hang

    .globl __bss_start
    .globl __bss_end
    .globl _stack_top
    .globl __global_pointer__
