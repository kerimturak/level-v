/* ============================================================
 * Ceres-V Linker Script for Embench Benchmarks
 * ============================================================
 * Memory layout for RV32IMC processor
 */

OUTPUT_ARCH(riscv)
ENTRY(_start)

/* Memory Configuration */
MEMORY
{
    /* ROM/Flash area for code - 1MB */
    ROM   (rx)  : ORIGIN = 0x80000000, LENGTH = 1M
    
    /* RAM area for data - 512KB */
    RAM   (rwx) : ORIGIN = 0x80100000, LENGTH = 512K
}

/* Stack and heap sizes */
_stack_size = 8K;
_heap_size  = 16K;

SECTIONS
{
    /* Code section in ROM */
    .text : ALIGN(4)
    {
        *(.text.init)
        *(.text.unlikely .text.unlikely.*)
        *(.text.startup .text.startup.*)
        *(.text .text.*)
        *(.gnu.linkonce.t.*)
        
        . = ALIGN(4);
        
        /* Read-only data can go with code */
        *(.rodata .rodata.*)
        *(.gnu.linkonce.r.*)
        *(.srodata .srodata.*)
        
        . = ALIGN(4);
    } > ROM
    
    /* Exception handling (C++) */
    .eh_frame : ALIGN(4)
    {
        KEEP(*(.eh_frame))
    } > ROM
    
    /* Global pointer for small data optimization */
    .sdata : ALIGN(4)
    {
        __global_pointer$ = . + 0x800;
        *(.sdata .sdata.*)
        *(.gnu.linkonce.s.*)
    } > RAM AT > ROM
    
    /* Initialized data - stored in ROM, copied to RAM */
    .data : ALIGN(4)
    {
        _data_start = .;
        *(.data .data.*)
        *(.gnu.linkonce.d.*)
        . = ALIGN(4);
        _data_end = .;
    } > RAM AT > ROM
    
    /* Load address for data section */
    _data_lma = LOADADDR(.data);
    
    /* Small BSS */
    .sbss : ALIGN(4)
    {
        *(.sbss .sbss.*)
        *(.gnu.linkonce.sb.*)
        *(.scommon)
    } > RAM
    
    /* Uninitialized data */
    .bss : ALIGN(4)
    {
        _bss_start = .;
        *(.bss .bss.*)
        *(.gnu.linkonce.b.*)
        *(COMMON)
        . = ALIGN(4);
        _bss_end = .;
    } > RAM
    
    /* Heap section */
    .heap : ALIGN(8)
    {
        . = ALIGN(8);
        _heap_start = .;
        . += _heap_size;
        _heap_end = .;
    } > RAM
    
    /* Stack section (grows downward) */
    .stack : ALIGN(16)
    {
        . = ALIGN(16);
        _stack_bottom = .;
        . += _stack_size;
        _stack_top = .;
    } > RAM
    
    /* Debug info (optional) */
    .comment 0 : { *(.comment) }
    .debug          0 : { *(.debug) }
    .line           0 : { *(.line) }
    .debug_srcinfo  0 : { *(.debug_srcinfo) }
    .debug_sfnames  0 : { *(.debug_sfnames) }
    .debug_aranges  0 : { *(.debug_aranges) }
    .debug_pubnames 0 : { *(.debug_pubnames) }
    .debug_info     0 : { *(.debug_info .gnu.linkonce.wi.*) }
    .debug_abbrev   0 : { *(.debug_abbrev) }
    .debug_line     0 : { *(.debug_line .debug_line.* .debug_line_end ) }
    .debug_frame    0 : { *(.debug_frame) }
    .debug_str      0 : { *(.debug_str) }
    .debug_loc      0 : { *(.debug_loc) }
    .debug_macinfo  0 : { *(.debug_macinfo) }
    .debug_ranges   0 : { *(.debug_ranges) }
    
    /* Discard unwanted sections */
    /DISCARD/ :
    {
        *(.note.*)
        *(.iplt)
        *(.igot.plt)
        *(.rel.dyn)
        *(.rela.dyn)
    }
}

/* Provide symbols for C library */
PROVIDE(__stack = _stack_top);
PROVIDE(__heap_start = _heap_start);
PROVIDE(__heap_end = _heap_end);
PROVIDE(_end = _bss_end);
