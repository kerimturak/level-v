#!/usr/bin/env python3
"""
make_symmetric_mem.py — 32-bit HEX → 128-bit + mirror symmetric MEM

Her 4 satırı (4x32-bit = 128-bit) bir cache line olarak birleştirir.
Ardından aynı satırın "ayna simetrisini" (ters kelime sırası) ikinci satır olarak ekler.

Örnek:
  Girdi:
    00000000
    41014081
    42014181
    43014281

  Çıktı:
    43014281420141814101408100000000
    00000000410140814201418143014281
"""

import sys
from pathlib import Path

def make_128bit_symmetric(lines):
    """Her 4 kelimeden bir 128-bit line oluşturur, ardından mirror ekler."""
    words = [l.strip() for l in lines if l.strip()]
    mem_lines = []
    for i in range(0, len(words), 4):
        group = words[i:i+4]
        if len(group) < 4:
            group += ["00000000"] * (4 - len(group))
        # 128-bit satır (word0 sağda olacak şekilde)
        normal = "".join(group[::-1])
        mirror = "".join(group)
        mem_lines.append(normal.lower())
        mem_lines.append(mirror.lower())
    return mem_lines

def main():
    if len(sys.argv) != 3:
        print("Usage: python3 make_symmetric_mem.py input.hex output.mem")
        sys.exit(1)

    inp, outp = Path(sys.argv[1]), Path(sys.argv[2])
    if not inp.exists():
        sys.exit(f"❌ Input file not found: {inp}")

    lines = inp.read_text().splitlines()
    mem_lines = make_128bit_symmetric(lines)
    outp.write_text("\n".join(mem_lines) + "\n")
    print(f"✅ Created {outp} ({len(mem_lines)} lines, with mirror symmetry)")

if __name__ == "__main__":
    main()
