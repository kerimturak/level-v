/* ============================================================
 * Ceres-V Linker Script for Embench - 32KB Memory
 * Embench benchmarks are small embedded apps
 * ============================================================
 */

OUTPUT_ARCH(riscv)
ENTRY(_start)

MEMORY
{
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 32K
}

_stack_size = 4K;   /* Embench benchmarks need decent stack */
_heap_size  = 4K;   /* Some tests use malloc */

SECTIONS
{
    . = 0x80000000;
    
    /* Code section */
    .text : ALIGN(4)
    {
        *(.text.init)
        *(.text.startup*)
        *(.text.unlikely*)
        *(.text*)
        *(.gnu.linkonce.t.*)
    } > RAM
    
    /* Read-only data */
    .rodata : ALIGN(4)
    {
        *(.rodata*)
        *(.srodata*)
        *(.gnu.linkonce.r.*)
    } > RAM
    
    /* Exception handling frames */
    .eh_frame : ALIGN(4)
    {
        KEEP(*(.eh_frame))
        KEEP(*(.eh_frame_hdr))
    } > RAM
    
    /* Small data with global pointer */
    .sdata : ALIGN(4)
    {
        __global_pointer$ = . + 0x800;
        *(.sdata*)
        *(.gnu.linkonce.s.*)
    } > RAM
    
    /* Initialized data */
    .data : ALIGN(4)
    {
        _data_start = .;
        *(.data*)
        *(.gnu.linkonce.d.*)
        _data_end = .;
    } > RAM
    
    /* Small BSS */
    .sbss : ALIGN(4)
    {
        *(.sbss*)
        *(.gnu.linkonce.sb.*)
        *(.scommon)
    } > RAM
    
    /* Uninitialized data */
    .bss : ALIGN(4)
    {
        _bss_start = .;
        *(.bss*)
        *(.gnu.linkonce.b.*)
        *(COMMON)
        _bss_end = .;
    } > RAM
    
    /* Heap for malloc */
    .heap (NOLOAD) : ALIGN(8)
    {
        _heap_start = .;
        . += _heap_size;
        _heap_end = .;
    } > RAM
    
    /* Stack */
    .stack (NOLOAD) : ALIGN(16)
    {
        _stack_bottom = .;
        . += _stack_size;
        _stack_top = .;
    } > RAM
    
    _end = .;
    
    /* Memory check */
    ASSERT(. <= 0x80008000, "ERROR: Embench exceeds 32KB memory!")
    
    /* Discard sections */
    /DISCARD/ :
    {
        *(.note*)
        *(.comment)
        *(.eh_frame*)
        *(.iplt)
        *(.igot*)
        *(.rel*)
        *(.rela*)
    }
}

/* C library symbols */
PROVIDE(__stack = _stack_top);
PROVIDE(__heap_start = _heap_start);
PROVIDE(__heap_end = _heap_end);
PROVIDE(_end = _bss_end);
PROVIDE(end = _bss_end);