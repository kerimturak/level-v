/* ============================================================
 * Ceres-V Linker Script for RISCV-DV Tests
 * ============================================================
 */

OUTPUT_ARCH(riscv)
ENTRY(_start)

MEMORY
{
    ROM   (rx)  : ORIGIN = 0x80000000, LENGTH = 1M
    RAM   (rwx) : ORIGIN = 0x80100000, LENGTH = 512K
}

SECTIONS
{
    .text : ALIGN(4)
    {
        *(.text.init)
        *(.text .text.*)
        *(.rodata .rodata.*)
        . = ALIGN(4);
    } > ROM
    
    .data : ALIGN(4)
    {
        __global_pointer$ = . + 0x800;
        *(.sdata .sdata.*)
        *(.data .data.*)
        . = ALIGN(4);
    } > RAM AT > ROM
    
    .bss : ALIGN(4)
    {
        *(.sbss .sbss.*)
        *(.bss .bss.*)
        *(COMMON)
        . = ALIGN(4);
    } > RAM
    
    .stack : ALIGN(16)
    {
        . = . + 8K;
        _stack_top = .;
    } > RAM
    
    /DISCARD/ : { *(.note.*) *(.comment) }
}

PROVIDE(__stack = _stack_top);
