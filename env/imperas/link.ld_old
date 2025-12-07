/* RISC-V Imperas Test Linker Script for Ceres Processor */
/* Ceres-V RV32IMC_Zicsr Processor */

OUTPUT_ARCH("riscv")
ENTRY(rvtest_entry_point)

/* Memory Layout for Ceres */
MEMORY
{
    RAM   (rwx) : ORIGIN = 0x80000000, LENGTH = 2M
}

SECTIONS
{
    /* Code section - starts at RAM base */
    . = 0x80000000;
    
    .text.init : {
        *(.text.init)
    } > RAM
    
    . = ALIGN(0x1000);
    
    .tohost : {
        *(.tohost)
    } > RAM
    
    . = ALIGN(0x1000);
    
    .text : {
        *(.text)
        *(.text.*)
    } > RAM
    
    . = ALIGN(0x1000);
    
    /* Read-only data */
    .rodata : {
        *(.rodata)
        *(.rodata.*)
    } > RAM
    
    . = ALIGN(0x1000);
    
    /* Data section */
    .data : {
        _data_start = .;
        *(.data)
        *(.data.*)
        _data_end = .;
    } > RAM
    
    /* BSS section */
    .bss : {
        _bss_start = .;
        *(.bss)
        *(.bss.*)
        *(.sbss)
        *(.sbss.*)
        *(COMMON)
        _bss_end = .;
    } > RAM
    
    . = ALIGN(16);
    
    /* Stack */
    .stack : {
        . = . + 4K;
        _stack_top = .;
    } > RAM
    
    _end = .;
}
