#!/usr/bin/env python3
"""
hex_to_mem.py — Convert Verilog HEX (from objcopy) → 32-bit MEM format
-----------------------------------------------------------------------

For wrapper_ram which uses 32-bit word-based memory organization.
Each line in output is a single 32-bit word (8 hex chars).

Usage:
    python3 hex_to_mem.py input.hex output.mem
"""

import sys


def parse_objcopy_hex_bytes(path):
    """
    Verilog HEX dosyasını byte-level memory haritasına çevirir.
    
    Returns:
        mem_bytes: {offset: byte_value} dictionary
        base_addr: İlk görülen adres
        max_addr: En yüksek görülen adres
    """
    mem_bytes = {}
    current_addr = None
    base_addr = None
    max_addr = 0

    with open(path) as f:
        for raw_line in f:
            line = raw_line.strip()
            if not line:
                continue

            # Adres satırı
            if line.startswith("@"):
                current_addr = int(line[1:], 16)
                if base_addr is None:
                    base_addr = current_addr
                if current_addr > max_addr:
                    max_addr = current_addr
                continue

            if current_addr is None:
                continue

            # Data satırı
            parts = line.split()
            for p in parts:
                if len(p) != 2:
                    continue

                try:
                    byte_val = int(p, 16)
                except ValueError:
                    continue

                offset = current_addr - base_addr
                mem_bytes[offset] = byte_val
                
                if current_addr > max_addr:
                    max_addr = current_addr

                current_addr += 1

    return mem_bytes, base_addr, max_addr


def bytes_to_32bit_lines(mem_bytes, base_addr, max_addr, word_bytes=4):
    """
    Byte-level memory haritasını 32-bit satırlar halinde döndürür.
    
    Args:
        mem_bytes: {offset: byte_value}
        base_addr: Base address
        max_addr: Maximum address seen
        word_bytes: Bytes per word (4 for 32-bit)
    
    Returns:
        List of hex strings (32-bit words)
    """
    if not mem_bytes and max_addr == 0:
        raise ValueError("Empty memory map")

    # Memory boyutunu hesapla
    memory_size = max_addr - base_addr + 1
    
    # 4-byte boundary'ye yuvarla
    num_words = (memory_size + word_bytes - 1) // word_bytes
    
    lines = []

    # Her 4-byte word için
    for word_idx in range(num_words):
        word_offset = word_idx * word_bytes

        # Little-endian: düşük adres = LSB
        b0 = mem_bytes.get(word_offset + 0, 0)
        b1 = mem_bytes.get(word_offset + 1, 0)
        b2 = mem_bytes.get(word_offset + 2, 0)
        b3 = mem_bytes.get(word_offset + 3, 0)

        word_val = (b3 << 24) | (b2 << 16) | (b1 << 8) | b0
        lines.append(f"{word_val:08x}")

    return lines


def convert(input_hex, output_mem):
    """
    HEX → 32-bit MEM dönüşümü
    """
    mem_bytes, base_addr, max_addr = parse_objcopy_hex_bytes(input_hex)
    lines = bytes_to_32bit_lines(mem_bytes, base_addr, max_addr)

    with open(output_mem, "w") as f:
        f.write("\n".join(lines))
        f.write("\n")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python3 hex_to_mem.py input.hex output.mem")
        sys.exit(1)

    convert(sys.argv[1], sys.argv[2])