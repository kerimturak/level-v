/*
 * Simple linker script for Ceres-V baremetal CoreMark
 * Everything in one contiguous RAM block
 */

OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY
{
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 64K
}

SECTIONS
{
    . = 0x80000000;

    /* Everything in order: text, rodata, data, bss, heap, stack */

    .text : ALIGN(4)
    {
        KEEP(*(.text.init))
        *(.text.startup)
        *(.text*)
        *(.rodata*)
        *(.srodata*)
    } > RAM

    .data : ALIGN(4)
    {
        _data_start = .;
        *(.data*)
        *(.sdata*)
        _data_end = .;
    } > RAM

    _data_lma = LOADADDR(.data);

    .bss (NOLOAD) : ALIGN(4)
    {
        _bss_start = .;
        *(.bss*)
        *(.sbss*)
        *(COMMON)
        _bss_end = .;
    } > RAM

    /* Global pointer for small data */
    __global_pointer$ = _data_start + (_bss_end - _data_start) / 2;

    /* Heap */
    . = ALIGN(4);
    _heap_start = .;
    . += 8K;
    _heap_end = .;

    /* Stack */
    . = ALIGN(8);
    . += 4K;
    _stack_top = .;

    _end = .;
}
