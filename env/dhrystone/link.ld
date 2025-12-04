/* ============================================================
 * Ceres-V Linker Script for Dhrystone
 * ============================================================
 */

OUTPUT_ARCH(riscv)
ENTRY(_start)

MEMORY
{
    ROM   (rx)  : ORIGIN = 0x80000000, LENGTH = 1M
    RAM   (rwx) : ORIGIN = 0x80100000, LENGTH = 512K
}

_stack_size = 8K;
_heap_size  = 16K;

SECTIONS
{
    .text : ALIGN(4)
    {
        *(.text.init)
        *(.text .text.*)
        *(.rodata .rodata.*)
        . = ALIGN(4);
    } > ROM
    
    .sdata : ALIGN(4)
    {
        __global_pointer$ = . + 0x800;
        *(.sdata .sdata.*)
    } > RAM AT > ROM
    
    .data : ALIGN(4)
    {
        _data_start = .;
        *(.data .data.*)
        . = ALIGN(4);
        _data_end = .;
    } > RAM AT > ROM
    
    _data_lma = LOADADDR(.data);
    
    .sbss : ALIGN(4)
    {
        *(.sbss .sbss.*)
    } > RAM
    
    .bss : ALIGN(4)
    {
        _bss_start = .;
        *(.bss .bss.*)
        *(COMMON)
        . = ALIGN(4);
        _bss_end = .;
    } > RAM
    
    .heap : ALIGN(8)
    {
        _heap_start = .;
        . += _heap_size;
        _heap_end = .;
    } > RAM
    
    .stack : ALIGN(16)
    {
        _stack_bottom = .;
        . += _stack_size;
        _stack_top = .;
    } > RAM
    
    /DISCARD/ :
    {
        *(.note.*)
        *(.comment)
    }
}

PROVIDE(__stack = _stack_top);
