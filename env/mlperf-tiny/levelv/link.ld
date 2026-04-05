/*
 * Auto-generated Linker Script for level-V
 * ISA: RV32IMC_Zicsr
 * Generated from memory_map.yaml
 * 
 * Memory Layout:
 *   ROM: 0x80000000 - 0x80007FFF (32K)
 *   RAM: 0x80000000 - 0x8000FFFF (64K)
 *   Stack: 8K
 *   Heap: 48K
 */

OUTPUT_ARCH("riscv")
ENTRY(_start)

/* Memory Regions */
MEMORY
{
    ROM (rx)  : ORIGIN = 0x80000000, LENGTH = 32K
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 64K
}

/* Stack size */
_stack_size = 8K;
_heap_size = 48K;

SECTIONS
{
    /* Code section - starts at ROM origin */
    .text : ALIGN(4)
    {
        _text_start = .;
        *(.text.init)      /* Startup code first */
        *(.text .text.*)   /* All other code */
        *(.rodata .rodata.*)  /* Read-only data */
        . = ALIGN(4);
        _text_end = .;
        _etext = .;
    } > ROM

    /* Initialized data section */
    .data : ALIGN(4)
    {
        _data_start = .;
        *(.data .data.*)
        *(.sdata .sdata.*)
        . = ALIGN(4);
        _data_end = .;
    } > RAM AT > ROM

    /* Data load address (for copying from ROM to RAM) */
    _data_load = LOADADDR(.data);

    /* Uninitialized data section (BSS) */
    .bss (NOLOAD) : ALIGN(4)
    {
        _bss_start = .;
        *(.bss .bss.*)
        *(.sbss .sbss.*)
        *(COMMON)
        . = ALIGN(4);
        _bss_end = .;
    } > RAM

    /* Global pointer for efficient small data access */
    PROVIDE(__global_pointer$ = _data_start + 0x800);

    /* Heap section */
    .heap (NOLOAD) : ALIGN(8)
    {
        _heap_start = .;
        . = . + _heap_size;
        _heap_end = .;
    } > RAM

    /* Stack section - at end of RAM */
    .stack (NOLOAD) : ALIGN(16)
    {
        _stack_bottom = .;
        . = . + _stack_size;
        _stack_top = .;
    } > RAM

    /* End of used memory */
    _end = .;
    PROVIDE(end = .);

    /* Discard unwanted sections */
    /DISCARD/ :
    {
        *(.comment)
        *(.note*)
        *(.eh_frame*)
        *(.riscv.attributes)
    }
}

/* Assertions to catch memory overflow */
ASSERT(_stack_top <= 0x80010000, "Stack overflow - increase RAM or decrease stack size")
ASSERT(_end <= 0x80010000, "RAM overflow - program too large")
