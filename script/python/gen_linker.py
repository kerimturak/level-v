#!/usr/bin/env python3
"""
Linker Script Generator for Ceres-V
====================================
Memory map YAML dosyasından linker script oluşturur.

Kullanım:
    python3 gen_linker.py memory_map.yaml output.ld
    python3 gen_linker.py memory_map.yaml output.ld --header output.h
"""

import sys
import argparse
import yaml
from pathlib import Path


def parse_size(size_str):
    """
    Boyut string'ini byte'a çevirir.
    Örnek: "32K" -> 32768, "64M" -> 67108864
    """
    if isinstance(size_str, int):
        return size_str
    
    size_str = str(size_str).strip().upper()
    
    multipliers = {
        'K': 1024,
        'KB': 1024,
        'M': 1024 * 1024,
        'MB': 1024 * 1024,
        'G': 1024 * 1024 * 1024,
        'GB': 1024 * 1024 * 1024,
    }
    
    for suffix, mult in multipliers.items():
        if size_str.endswith(suffix):
            return int(size_str[:-len(suffix)]) * mult
    
    # Hex veya decimal
    if size_str.startswith('0X'):
        return int(size_str, 16)
    return int(size_str)


def format_hex(value):
    """Değeri hex formatında döndürür."""
    return f"0x{value:08X}"


def format_size(size_bytes):
    """Byte'ı okunabilir formata çevirir."""
    if size_bytes >= 1024 * 1024:
        return f"{size_bytes // (1024*1024)}M"
    elif size_bytes >= 1024:
        return f"{size_bytes // 1024}K"
    return str(size_bytes)


def generate_linker_script(config):
    """YAML config'den linker script oluşturur."""
    
    # Memory bölgelerini parse et
    memory = config.get('memory', {})
    stack_config = config.get('stack', {})
    heap_config = config.get('heap', {})
    entry = config.get('entry', '_start')
    processor = config.get('processor', {})
    
    rom = memory.get('rom', {})
    ram = memory.get('ram', {})
    
    rom_origin = rom.get('origin', 0x80000000)
    rom_length = parse_size(rom.get('length', '32K'))
    rom_type = rom.get('type', 'rx')
    
    ram_origin = ram.get('origin', 0x80008000)
    ram_length = parse_size(ram.get('length', '32K'))
    ram_type = ram.get('type', 'rwx')
    
    stack_size = parse_size(stack_config.get('size', '4K'))
    heap_size = parse_size(heap_config.get('size', '0'))
    
    # Linker script oluştur
    ld_script = f'''/*
 * Auto-generated Linker Script for {processor.get('name', 'RISC-V')}
 * ISA: {processor.get('isa', 'RV32I')}
 * Generated from memory_map.yaml
 * 
 * Memory Layout:
 *   ROM: {format_hex(rom_origin)} - {format_hex(rom_origin + rom_length - 1)} ({format_size(rom_length)})
 *   RAM: {format_hex(ram_origin)} - {format_hex(ram_origin + ram_length - 1)} ({format_size(ram_length)})
 *   Stack: {format_size(stack_size)}
 *   Heap: {format_size(heap_size)}
 */

OUTPUT_ARCH("riscv")
ENTRY({entry})

/* Memory Regions */
MEMORY
{{
    ROM ({rom_type})  : ORIGIN = {format_hex(rom_origin)}, LENGTH = {format_size(rom_length)}
    RAM ({ram_type}) : ORIGIN = {format_hex(ram_origin)}, LENGTH = {format_size(ram_length)}
}}

/* Stack size */
_stack_size = {format_size(stack_size)};
_heap_size = {format_size(heap_size)};

SECTIONS
{{
    /* Code section - starts at ROM origin */
    .text : ALIGN(4)
    {{
        _text_start = .;
        *(.text.init)      /* Startup code first */
        *(.text .text.*)   /* All other code */
        *(.rodata .rodata.*)  /* Read-only data */
        . = ALIGN(4);
        _text_end = .;
        _etext = .;
    }} > ROM

    /* Initialized data section */
    .data : ALIGN(4)
    {{
        _data_start = .;
        *(.data .data.*)
        *(.sdata .sdata.*)
        . = ALIGN(4);
        _data_end = .;
    }} > RAM AT > ROM

    /* Data load address (for copying from ROM to RAM) */
    _data_load = LOADADDR(.data);

    /* Uninitialized data section (BSS) */
    .bss (NOLOAD) : ALIGN(4)
    {{
        _bss_start = .;
        *(.bss .bss.*)
        *(.sbss .sbss.*)
        *(COMMON)
        . = ALIGN(4);
        _bss_end = .;
    }} > RAM

    /* Global pointer for efficient small data access */
    PROVIDE(__global_pointer$ = _data_start + 0x800);

    /* Heap section */
    .heap (NOLOAD) : ALIGN(8)
    {{
        _heap_start = .;
        . = . + _heap_size;
        _heap_end = .;
    }} > RAM

    /* Stack section - at end of RAM */
    .stack (NOLOAD) : ALIGN(16)
    {{
        _stack_bottom = .;
        . = . + _stack_size;
        _stack_top = .;
    }} > RAM

    /* End of used memory */
    _end = .;
    PROVIDE(end = .);

    /* Discard unwanted sections */
    /DISCARD/ :
    {{
        *(.comment)
        *(.note*)
        *(.eh_frame*)
        *(.riscv.attributes)
    }}
}}

/* Assertions to catch memory overflow */
ASSERT(_stack_top <= {format_hex(ram_origin + ram_length)}, "Stack overflow - increase RAM or decrease stack size")
ASSERT(_end <= {format_hex(ram_origin + ram_length)}, "RAM overflow - program too large")
'''
    
    return ld_script


def generate_header_file(config):
    """YAML config'den C header dosyası oluşturur."""
    
    processor = config.get('processor', {})
    clock = config.get('clock', {})
    memory = config.get('memory', {})
    peripherals = config.get('peripherals', {})
    uart_config = config.get('uart', {})
    stack_config = config.get('stack', {})
    
    cpu_hz = clock.get('cpu_hz', 50000000)
    baud_rate = uart_config.get('baud_rate', 115200)
    
    rom = memory.get('rom', {})
    ram = memory.get('ram', {})
    
    header = f'''/*
 * Auto-generated Hardware Definitions for {processor.get('name', 'RISC-V')}
 * ISA: {processor.get('isa', 'RV32I')}
 * Generated from memory_map.yaml
 */

#ifndef _MEMORY_MAP_H_
#define _MEMORY_MAP_H_

#include <stdint.h>

/* ============================================================ */
/* Clock Configuration */
/* ============================================================ */
#define CPU_CLK              {cpu_hz}UL    /* {cpu_hz // 1000000} MHz */
#define CLOCKS_PER_SEC       CPU_CLK
#define BAUD_RATE            {baud_rate}

/* ============================================================ */
/* Memory Regions */
/* ============================================================ */
#define ROM_BASE             {format_hex(rom.get('origin', 0x80000000))}
#define ROM_SIZE             {format_hex(parse_size(rom.get('length', '32K')))}
#define RAM_BASE             {format_hex(ram.get('origin', 0x80008000))}
#define RAM_SIZE             {format_hex(parse_size(ram.get('length', '32K')))}
#define STACK_SIZE           {format_hex(parse_size(stack_config.get('size', '4K')))}

'''
    
    # Peripheral tanımları
    for periph_name, periph in peripherals.items():
        base = periph.get('base', 0)
        header += f'''/* ============================================================ */
/* {periph_name.upper()} Peripheral */
/* ============================================================ */
#define {periph_name.upper()}_BASE         {format_hex(base)}

'''
        # Register tanımları
        registers = periph.get('registers', {})
        for reg_name, reg in registers.items():
            offset = reg.get('offset', 0)
            desc = reg.get('description', '')
            macro_name = f"{periph_name.upper()}_{reg_name.upper()}"
            header += f'#define {macro_name:20} (*(volatile uint32_t*)({format_hex(base + offset)}))  /* {desc} */\n'
        header += '\n'
    
    # UART status bit tanımları
    if 'uart' in peripherals:
        header += '''/* UART Status Register Bits */
#define UART_STATUS_TX_FULL  (1 << 0)
#define UART_STATUS_RX_FULL  (1 << 1)
#define UART_STATUS_TX_EMPTY (1 << 2)
#define UART_STATUS_RX_EMPTY (1 << 3)

/* UART Control Register Bits */
#define UART_CTRL_TX_EN      (1 << 0)
#define UART_CTRL_RX_EN      (1 << 1)

'''
    
    header += '''#endif /* _MEMORY_MAP_H_ */
'''
    
    return header


def main():
    parser = argparse.ArgumentParser(
        description='Generate linker script from memory map YAML'
    )
    parser.add_argument('input', help='Input YAML file')
    parser.add_argument('output', help='Output linker script (.ld)')
    parser.add_argument('--header', '-H', help='Also generate C header file')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')
    
    args = parser.parse_args()
    
    # YAML dosyasını oku
    input_path = Path(args.input)
    if not input_path.exists():
        print(f"Error: Input file not found: {args.input}", file=sys.stderr)
        sys.exit(1)
    
    with open(input_path, 'r') as f:
        config = yaml.safe_load(f)
    
    if args.verbose:
        print(f"Loaded config from: {args.input}")
        print(f"Processor: {config.get('processor', {}).get('name', 'Unknown')}")
    
    # Linker script oluştur
    ld_script = generate_linker_script(config)
    
    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    
    with open(output_path, 'w') as f:
        f.write(ld_script)
    
    print(f"Generated: {args.output}")
    
    # Header dosyası oluştur (opsiyonel)
    if args.header:
        header = generate_header_file(config)
        header_path = Path(args.header)
        header_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(header_path, 'w') as f:
            f.write(header)
        
        print(f"Generated: {args.header}")
    
    return 0


if __name__ == '__main__':
    sys.exit(main())
