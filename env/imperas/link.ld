/* RISC-V Imperas Test Linker Script for Ceres Processor */
/* Ceres-V RV32IMC_Zicsr Processor - Optimized Compact Layout */

OUTPUT_ARCH("riscv")
ENTRY(rvtest_entry_point)

/* Memory Layout for Ceres */
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
        *(.text.startup)
    } > RAM
    
    /* Read-only data immediately after code */
    .rodata : ALIGN(4) {
        *(.rodata)
        *(.rodata.*)
        *(.srodata)
        *(.srodata.*)
    } > RAM
    
    /* Data section - 8-byte align for critical structures */
    .data : ALIGN(8) {
        _data_start = .;
        
        /* Imperas test interface structures */
        *(.tohost)
        . = ALIGN(8);
        
        /* Regular data */
        *(.data)
        *(.data.*)
        *(.sdata)
        *(.sdata.*)
        
        /* Signature area for Imperas */
        . = ALIGN(8);
        begin_signature = .;
        *(.signature)
        end_signature = .;
        
        . = ALIGN(8);
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
    
    /* Stack - reasonable size for tests */
    .stack : ALIGN(16) {
        . = . + 0x1000;      /* 4KB stack */
        _stack_top = .;
        _sp = .;             /* Stack pointer symbol */
    } > RAM
    
    _end = .;
    _heap_start = .;
    
    /* Symbol exports for Imperas framework */
    PROVIDE(tohost = ADDR(.data));
    PROVIDE(fromhost = tohost + 8);
    
    /* Debug sections (not loaded into memory) */
    .comment 0 : { *(.comment) }
    .debug_info 0 : { *(.debug_info) }
    .debug_abbrev 0 : { *(.debug_abbrev) }
    .debug_line 0 : { *(.debug_line) }
    .debug_str 0 : { *(.debug_str) }
    .debug_frame 0 : { *(.debug_frame) }
}