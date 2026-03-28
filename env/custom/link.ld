/* Level-V bare-metal custom tests (sim/test/custom/*.c)
 * Wider than CoreMark's 32 KiB so large test sources (e.g. cache_test) link.
 * Match FPGA: rtl/pkg/level_param.sv WRAPPER_RAM_SIZE_KB must be >= LENGTH here.
 */
OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY
{
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 40K
}

SECTIONS
{
    . = 0x80000000;

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

    .bss : ALIGN(4)
    {
        _bss_start = .;
        *(.bss*)
        *(.sbss*)
        *(COMMON)
        _bss_end = .;
    } > RAM

    __global_pointer$ = _data_start + (_bss_end - _data_start) / 2;

    .heap (NOLOAD) : ALIGN(4)
    {
        _heap_start = .;
        . += 4K;
        _heap_end = .;
    } > RAM

    .stack (NOLOAD) : ALIGN(8)
    {
        _stack_bottom = .;
        . += 4K;
        _stack_top = .;
    } > RAM

    _end = .;

    ASSERT(. <= 0x8000A000, "ERROR: Custom test exceeds 40KB RAM in env/custom/link.ld")
}
