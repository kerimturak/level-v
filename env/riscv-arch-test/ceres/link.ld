/* RISC-V Architecture Test Linker Script for Ceres Processor */
/* Optimized for compact memory layout */

OUTPUT_ARCH("riscv")
ENTRY(rvtest_entry_point)

MEMORY
{
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 2M
}

SECTIONS
{
    . = 0x80000000;
    
    /* Code section - tightly packed */
    .text : {
        *(.text.init)
        . = ALIGN(4);
        *(.text)
        *(.text.*)
    } > RAM
    
    /* Read-only data immediately after code */
    .rodata : ALIGN(4) {
        *(.rodata)
        *(.rodata.*)
    } > RAM
    
    /* Data section - 8-byte align for tohost/fromhost */
    .data : ALIGN(8) {
        _data_start = .;
        *(.tohost)           /* tohost/fromhost here */
        . = ALIGN(8);
        begin_regstate = .;
        . += 128;            /* regstate space */
        end_regstate = .;
        . = ALIGN(8);
        begin_signature = .; /* signature space */
        *(.data)
        *(.data.*)
        . = ALIGN(8);
        end_signature = .;
        _data_end = .;
    } > RAM
    
    /* BSS section */
    .bss : ALIGN(8) {
        _bss_start = .;
        *(.bss)
        *(.bss.*)
        *(.sbss)
        *(.sbss.*)
        *(COMMON)
        . = ALIGN(8);
        _bss_end = .;
    } > RAM
    
    /* Stack - minimal space */
    .stack : ALIGN(16) {
        . = . + 0x1000;      /* 4KB stack - testler için yeterli */
        _stack_top = .;
    } > RAM
    
    _end = .;
    
    /* Symbol exports for framework */
    PROVIDE(tohost = ADDR(.data));
    PROVIDE(fromhost = tohost + 8);
}