/* ============================================================
 * Ceres-V Linker Script for Torture Tests - 32KB Memory
 * Torture tests generate large code, need more space
 * ============================================================
 */

OUTPUT_ARCH(riscv)
ENTRY(_start)

MEMORY
{
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 32K
}

_stack_size = 2K;   /* Torture testler çok stack kullanmaz */

SECTIONS
{
    . = 0x80000000;
    
    /* Code section - torture tests büyük kod üretir */
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
    
    /* Data with global pointer */
    .sdata : ALIGN(4)
    {
        __global_pointer$ = . + 0x800;
        *(.sdata*)
    } > RAM
    
    .data : ALIGN(4)
    {
        _data_start = .;
        *(.data*)
        _data_end = .;
    } > RAM
    
    /* BSS section */
    .sbss : ALIGN(4)
    {
        *(.sbss*)
    } > RAM
    
    .bss : ALIGN(4)
    {
        _bss_start = .;
        *(.bss*)
        *(COMMON)
        _bss_end = .;
    } > RAM
    
    /* Stack - torture tests shallow call depth */
    .stack (NOLOAD) : ALIGN(8)
    {
        _stack_bottom = .;
        . += _stack_size;
        _stack_top = .;
    } > RAM
    
    _end = .;
    
    /* Memory check - torture tests can be LARGE! */
    ASSERT(. <= 0x80008000, "ERROR: Torture test exceeds 32KB memory!")
    
    /DISCARD/ :
    {
        *(.note*)
        *(.comment)
        *(.eh_frame*)
    }
}

PROVIDE(__stack = _stack_top);