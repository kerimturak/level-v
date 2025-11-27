#!/usr/bin/env python3
"""
hex_to_mem.py — Convert Verilog HEX (from objcopy) → 128-bit MEM (TCORE format)
-------------------------------------------------------------------------------

Düzeltilmiş sürüm:
- Memory boyutunu max adrese göre hesaplar (kullanılan byte'lara değil)
- Disassembly'de görülen tüm adreslere erişimi destekler
- Gap'leri doğru şekilde 0x00 ile doldurur
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
                # Max adresi güncelle
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
                
                # Max adresi güncelle
                if current_addr > max_addr:
                    max_addr = current_addr

                current_addr += 1

    return mem_bytes, base_addr, max_addr


def bytes_to_128bit_lines(mem_bytes, base_addr, max_addr, line_bytes=16, word_bytes=4):
    """
    Byte-level memory haritasını 128-bit satırlar halinde döndürür.
    
    Args:
        mem_bytes: {offset: byte_value}
        base_addr: Base address
        max_addr: Maximum address seen
        line_bytes: Bytes per line (16 for 128-bit)
        word_bytes: Bytes per word (4 for 32-bit)
    
    Returns:
        List of hex strings (128-bit lines)
    """
    if not mem_bytes and max_addr == 0:
        raise ValueError("Empty memory map")

    # Memory boyutunu hesapla
    # Max adresten base'i çıkar, sonra bir sonraki 16-byte boundary'ye yuvarla
    memory_size = max_addr - base_addr + 1
    
    # Disassembly'de görülen adresleri de kapsayacak şekilde genişlet
    # Örnek: 0x80006904 - 0x80000000 = 0x6904 = 26884 bytes
    # Bu da 1681 satır (26884 / 16 = 1680.25 -> 1681)
    
    # 16-byte boundary'ye yuvarla
    num_lines = (memory_size + line_bytes - 1) // line_bytes
    
    lines = []

    # Her 16-byte satır için
    for line_idx in range(num_lines):
        line_start = line_idx * line_bytes
        words = []

        # Her satırda 4 word (32-bit) var
        for w in range(4):
            word_offset = line_start + w * word_bytes

            # Little-endian: düşük adres = LSB
            b0 = mem_bytes.get(word_offset + 0, 0)
            b1 = mem_bytes.get(word_offset + 1, 0)
            b2 = mem_bytes.get(word_offset + 2, 0)
            b3 = mem_bytes.get(word_offset + 3, 0)

            word_val = (b3 << 24) | (b2 << 16) | (b1 << 8) | b0
            words.append(word_val)

        # TCORE format: w3 w2 w1 w0
        # w0 = en düşük adresli word (en sağda)
        w0, w1, w2, w3 = words
        line_hex = f"{w3:08x}{w2:08x}{w1:08x}{w0:08x}"
        lines.append(line_hex)

    return lines


def convert(input_hex, output_mem):
    """
    HEX → MEM dönüşümü
    """
    mem_bytes, base_addr, max_addr = parse_objcopy_hex_bytes(input_hex)
    lines = bytes_to_128bit_lines(mem_bytes, base_addr, max_addr)

    with open(output_mem, "w") as f:
        f.write("\n".join(lines))

    total_bytes = len(mem_bytes)
    memory_size = max_addr - base_addr + 1
    
    print(f"✅ Converted HEX → MEM")
    print(f"   Input         : {input_hex}")
    print(f"   Output        : {output_mem}")
    print(f"   Base addr     : 0x{base_addr:08x}")
    print(f"   Max addr      : 0x{max_addr:08x}")
    print(f"   Memory size   : {memory_size} bytes")
    print(f"   Bytes used    : {total_bytes} ({100*total_bytes/memory_size:.1f}%)")
    print(f"   Lines (128b)  : {len(lines)}")
    print(f"   Mem coverage  : 0x{base_addr:08x} - 0x{base_addr + len(lines)*16:08x}")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python3 hex_to_mem.py input.hex output.mem")
        sys.exit(1)

    convert(sys.argv[1], sys.argv[2])