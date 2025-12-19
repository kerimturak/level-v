/*
 * Linker script for Ceres-V RV32IMC_Zicsr processor
 * CoreMark benchmark - 16KB Total Memory (Tight Fit)
 */

OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY
{
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 16K
}

_stack_size = 2K;   /* Minimal stack */
_heap_size = 4K;    /* CoreMark için minimal heap */

SECTIONS
{
    . = 0x80000000;
    
    /* Code section - kompakt */
    .text : ALIGN(4)
    {
        *(.text.init)
        *(.text.startup)
        *(.text*)
    } > RAM

    /* Read-only data */
    .rodata : ALIGN(4)
    {
        *(.rodata*)
        *(.srodata*)
    } > RAM

    /* Data section - placed directly after rodata in baremetal */
    .data : ALIGN(4)
    {
        _data_start = .;
        *(.data*)
        *(.sdata*)
        _data_end = .;
    } > RAM

    /* LMA = VMA for baremetal (no separate flash/RAM) */
    _data_lma = _data_start;

    /* BSS section */
    .bss : ALIGN(4)
    {
        _bss_start = .;
        *(.bss*)
        *(.sbss*)
        *(COMMON)
        _bss_end = .;
    } > RAM

    /* Global pointer - middle of .sdata/.sbss for optimal addressing */
    PROVIDE(__global_pointer$ = MIN(_data_start + 0x800, _bss_end));

    /* Heap - CoreMark needs malloc */
    .heap (NOLOAD) : ALIGN(4)
    {
        _heap_start = .;
        . += _heap_size;
        _heap_end = .;
    } > RAM

    /* Stack */
    .stack (NOLOAD) : ALIGN(8)
    {
        . += _stack_size;
        _stack_top = .;
    } > RAM

    _end = .;
    
    /* Memory usage check */
    ASSERT(. <= 0x80004000, "ERROR: Program exceeds 16KB memory limit!")
}