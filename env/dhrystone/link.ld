/* ============================================================
 * level-V Linker Script for Dhrystone (RV32 bare metal; RAM size must fit -O3 + newlib-less image)
 * ============================================================
 */

OUTPUT_ARCH(riscv)
ENTRY(_start)

MEMORY
{
    /* ~19.4 KiB image (see: make levelv_memory_report); leave headroom */
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 20K
}

_stack_size = 2K;   /* Dhrystone için minimal */
_heap_size  = 2K;   /* Dhrystone heap kullanmaz ama yine de */

SECTIONS
{
    . = 0x80000000;
    
    /* Code section */
    .text : ALIGN(4)
    {
        *(.text.init)
        *(.text*)
    } > RAM
    
    /* Read-only data */
    .rodata : ALIGN(4)
    {
        *(.rodata*)
    } > RAM
    
    /* Small data with GP */
    .sdata : ALIGN(4)
    {
        __global_pointer$ = . + 0x800;
        *(.sdata*)
    } > RAM
    
    /* Data section (VMA = LMA: loaded image; crt0 copies _data_lma → _data_start) */
    .data : ALIGN(4)
    {
        _data_start = .;
        *(.data*)
        _data_end = .;
    } > RAM

    PROVIDE(_data_lma = _data_start);
    
    /* Small BSS */
    .sbss : ALIGN(4)
    {
        *(.sbss*)
    } > RAM
    
    /* BSS section */
    .bss : ALIGN(4)
    {
        _bss_start = .;
        *(.bss*)
        *(COMMON)
        _bss_end = .;
    } > RAM
    
    /* Heap (minimal) */
    .heap (NOLOAD) : ALIGN(4)
    {
        _heap_start = .;
        . += _heap_size;
        _heap_end = .;
    } > RAM
    
    /* Stack */
    .stack (NOLOAD) : ALIGN(8)
    {
        _stack_bottom = .;
        . += _stack_size;
        _stack_top = .;
    } > RAM
    
    _end = .;
    
    /* Memory check */
    ASSERT(. <= 0x80005000, "ERROR: Dhrystone exceeds 20KB RAM in link.ld")
    
    /DISCARD/ :
    {
        *(.note*)
        *(.comment)
        *(.eh_frame*)
    }
}

PROVIDE(__stack = _stack_top);