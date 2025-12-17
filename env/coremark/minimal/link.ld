/*
 * Minimal linker script for CoreMark on RISC-V
 * Base address: 0x80000000 (standard RISC-V DRAM)
 */

OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY
{
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 128K
}

SECTIONS
{
    . = 0x80000000;

    .text : {
        *(.text.start)
        *(.text*)
        *(.rodata*)
    } > RAM

    .data : {
        *(.data*)
        *(.sdata*)
    } > RAM

    .bss : {
        __bss_start = .;
        *(.bss*)
        *(.sbss*)
        *(COMMON)
        __bss_end = .;
    } > RAM

    . = ALIGN(16);
    __stack_start = .;
    . = . + 0x4000; /* 16KB stack */
    __stack_top = .;

    _end = .;
}
