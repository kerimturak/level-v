/*
 * Linker script for Ceres-V RV32IMC_Zicsr processor
 * CoreMark benchmark
 */

OUTPUT_ARCH("riscv")
ENTRY(_start)

/* Memory layout for Ceres-V */
MEMORY
{
    /* Code starts at 0x80000000 */
    ROM (rx)  : ORIGIN = 0x80000000, LENGTH = 64K
    /* Data/Stack area */
    RAM (rwx) : ORIGIN = 0x80010000, LENGTH = 64K
}

/* Stack size */
_stack_size = 8K;

SECTIONS
{
    /* Code section */
    .text : ALIGN(4)
    {
        *(.text.init)
        *(.text .text.*)
        *(.rodata .rodata.*)
        . = ALIGN(4);
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

    _data_load = LOADADDR(.data);

    /* Uninitialized data section (BSS) */
    .bss : ALIGN(4)
    {
        _bss_start = .;
        *(.bss .bss.*)
        *(.sbss .sbss.*)
        *(COMMON)
        . = ALIGN(4);
        _bss_end = .;
    } > RAM

    /* Global pointer for efficient access to small data */
    PROVIDE(__global_pointer$ = _data_start + 0x800);

    /* Stack at end of RAM */
    .stack (NOLOAD) : ALIGN(16)
    {
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
    }
}
