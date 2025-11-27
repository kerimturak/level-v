#!/usr/bin/env python3
"""
hex_to_mem.py — Convert Verilog HEX (from objcopy) → 128-bit MEM (TCORE format)
-------------------------------------------------------------------------------

Özellikler:
- Verilog HEX içindeki @address jump'larını korur.
- Adresler arasındaki boşlukları 0x00 ile doldurur.
- Varsayılan olarak memory boyutunu HEX içindeki en yüksek adrese göre hesaplar.
- İsteğe bağlı --end-addr ile, linker script’teki _end gibi bir son adrese kadar
  (örneğin .bss + .tbss dâhil) memory’yi uzatır ve bu kısmı da 0 ile doldurur.

TCORE formatı:
- Her satır 128-bit (16 byte) kabul edilir.
- 4 adet 32-bit word içerir.
- Little-endian: düşük adresli byte = LSB.
- Satır formatı: w3 w2 w1 w0 (w0 en düşük adresli word, satırın en SAĞINDA).
"""

import sys
import argparse


def parse_objcopy_hex_bytes(path):
    """
    Verilog HEX dosyasını byte-level memory haritasına çevirir.

    Returns:
        mem_bytes: {offset: byte_value} dictionary
            offset = (mutlak_adres - base_addr)
        base_addr: İlk görülen adres (mutlak)
        max_addr:  En yüksek görülen adres (mutlak, son dolu byte adresi)
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

            # Adres satırı ("@80000000" gibi)
            if line.startswith("@"):
                current_addr = int(line[1:], 16)
                if base_addr is None:
                    base_addr = current_addr
                # Adres marker'ı da max_addr hesabına giriyor (boş satır olsa bile)
                if current_addr > max_addr:
                    max_addr = current_addr
                continue

            # Adres gelmeden data görürsek, yoksay (korumalı davranış)
            if current_addr is None:
                continue

            # Data satırı (byte'lar: "13 05 00 00 ..." gibi)
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

                # current_addr: BU byte'ın adresi
                if current_addr > max_addr:
                    max_addr = current_addr

                current_addr += 1

    if base_addr is None:
        raise ValueError(f"No @address found in HEX file: {path}")

    return mem_bytes, base_addr, max_addr


def bytes_to_128bit_lines(
    mem_bytes,
    base_addr,
    max_addr,
    end_addr=None,
    line_bytes=16,
    word_bytes=4,
):
    """
    Byte-level memory haritasını 128-bit satırlar halinde döndürür.

    Args:
        mem_bytes : {offset: byte_value}
            offset = (mutlak_adres - base_addr)
        base_addr : İlk görülen mutlak adres
        max_addr  : HEX içinde görülen en yüksek mutlak adres (dolmuş son byte)
        end_addr  : (Opsiyonel) Mutlak son adres sınırı
                    - Linker script'teki _end sembolü için:
                      _end = ilk serbest adres -> son kullanılan byte = _end - 1
                    - Bu fonksiyon, end_addr'ı "son kullanılan byte adresi" olarak bekler.
        line_bytes: Satır başına byte (128-bit için 16)
        word_bytes: Word başına byte (32-bit word için 4)

    Returns:
        lines: List[str] — her eleman 128-bit satırın hex string karşılığı
    """
    if not mem_bytes and max_addr == 0:
        raise ValueError("Empty memory map")

    # En son dolu byte adresini belirle:
    last_used_addr = max_addr

    # Eğer bir upper bound verilmişse (ör: .bss sonu):
    if end_addr is not None:
        if end_addr < base_addr:
            raise ValueError(
                f"end_addr (0x{end_addr:08x}) < base_addr (0x{base_addr:08x})"
            )
        if end_addr > last_used_addr:
            # end_addr burada "son kullanılan byte" adresi olarak düşünülüyor.
            last_used_addr = end_addr

    # [base_addr, last_used_addr] aralığını kapsayacak memory boyutu
    memory_size = last_used_addr - base_addr + 1

    # 16-byte (128-bit) satır sayısı → yukarı yuvarla
    num_lines = (memory_size + line_bytes - 1) // line_bytes

    lines = []

    for line_idx in range(num_lines):
        line_start = line_idx * line_bytes  # base_addr'dan itibaren offset
        words = []

        # Her satırda 4 adet 32-bit word (w0..w3)
        for w in range(4):
            word_offset = line_start + w * word_bytes

            # Little-endian: düşük adres = LSB (b0)
            b0 = mem_bytes.get(word_offset + 0, 0)
            b1 = mem_bytes.get(word_offset + 1, 0)
            b2 = mem_bytes.get(word_offset + 2, 0)
            b3 = mem_bytes.get(word_offset + 3, 0)

            word_val = (b3 << 24) | (b2 << 16) | (b1 << 8) | b0
            words.append(word_val)

        # TCORE format: w3 w2 w1 w0 (w0 en düşük adresli word ve en sağda)
        w0, w1, w2, w3 = words
        line_hex = f"{w3:08x}{w2:08x}{w1:08x}{w0:08x}"
        lines.append(line_hex)

    return lines, memory_size, last_used_addr


def convert(input_hex, output_mem, end_addr_arg=None):
    """
    HEX → MEM dönüşümü.

    end_addr_arg:
        - None ise: sadece HEX içindeki max_addr'a kadar.
        - Değer verilirse:
            * Bu değer "son kullanılan byte adresi" olarak yorumlanır.
            * Örn: linker'da `_end` ilk serbest adres ise,
              skripte `_end - 1` verilmelidir.
    """
    mem_bytes, base_addr, max_addr = parse_objcopy_hex_bytes(input_hex)

    # end_addr_arg string'ini (hex/decimal) parse et
    end_addr = None
    if end_addr_arg is not None:
        s = end_addr_arg.strip().lower()
        if s.startswith("0x"):
            end_addr = int(s, 16)
        else:
            end_addr = int(s, 0)

    lines, memory_size, last_used_addr = bytes_to_128bit_lines(
        mem_bytes, base_addr, max_addr, end_addr=end_addr
    )

    with open(output_mem, "w") as f:
        f.write("\n".join(lines))

    total_bytes = len(mem_bytes)

    print(f"✅ Converted HEX → MEM")
    print(f"  Input        : {input_hex}")
    print(f"  Output       : {output_mem}")
    print(f"  Base addr    : 0x{base_addr:08x}")
    print(f"  HEX max addr : 0x{max_addr:08x}")
    print(f"  Used max addr: 0x{last_used_addr:08x}")
    print(f"  Memory size  : {memory_size} bytes")
    print(f"  Bytes used   : {total_bytes} "
          f"({100 * total_bytes / memory_size:.1f}%)")
    print(f"  Lines (128b) : {len(lines)}")
    print(
        f"  Mem coverage : 0x{base_addr:08x} - "
        f"0x{base_addr + len(lines) * 16 - 1:08x}"
    )


def main():
    parser = argparse.ArgumentParser(
        description="Convert Verilog HEX (objcopy --verilog-data) "
                    "to 128-bit MEM (TCORE)."
    )
    parser.add_argument("input_hex", help="Input HEX file (Verilog format)")
    parser.add_argument("output_mem", help="Output MEM file (128-bit lines)")
    parser.add_argument(
        "--end-addr",
        help=(
            "Optional absolute last used address (INCLUSIVE). "
            "Memory image base_addr..end_addr aralığını kapsar. "
            "Linker'daki _end ilk serbest adres ise, buraya (_end - 1) ver."
        ),
        default=None,
    )

    args = parser.parse_args()
    convert(args.input_hex, args.output_mem, args.end_addr)


if __name__ == "__main__":
    main()
