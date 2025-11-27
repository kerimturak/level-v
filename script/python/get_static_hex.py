#!/usr/bin/env python3
"""
get_static_hex.py — CERES Memory Image Reformatter (Advanced Version)
---------------------------------------------------------------------

Binary dosyayı bloklara ayırarak, her blok içindeki byte'ları ters çevirip
(endianness düzeltmesi) HEX formatında bir output dosyasına yazar.
İsteğe bağlı olarak bir log dosyası üretir.

Örnek:
    python3 get_static_hex.py -b 16 -o prog.hex -l prog.log prog.bin
"""

import sys
import argparse
from pathlib import Path

def main():
    parser = argparse.ArgumentParser(
        description="Binary → Reversed-block HEX converter (with optional logging)."
    )
    parser.add_argument("-b", "--block-size", type=int, required=True,
                        help="Blok boyutu (bayt cinsinden)")
    parser.add_argument("-o", "--output", type=str, required=True,
                        help="Çıkış hex dosyası")
    parser.add_argument("-l", "--logfile", type=str, default=None,
                        help="Opsiyonel log dosyası")
    parser.add_argument("binfile", help="Girdi binary dosyası")
    args = parser.parse_args()

    bs = args.block_size
    infile = Path(args.binfile)
    outfile = Path(args.output)
    logf = Path(args.logfile) if args.logfile else None

    # Input file okuma
    if not infile.exists():
        sys.exit(f"❌ Girdi dosyası bulunamadı: {infile}")

    try:
        data = infile.read_bytes()
    except Exception as e:
        sys.exit(f"❌ Dosya açılamadı: {e}")

    total_bytes = len(data)
    num_blocks = (total_bytes + bs - 1) // bs

    # Log dosyasını aç
    log = None
    if logf:
        try:
            log = logf.open("w")
            log.write("=== CERES Memory Reformatter Log ===\n")
            log.write(f"Girdi Dosyası   : {infile}\n")
            log.write(f"Çıkış Dosyası   : {outfile}\n")
            log.write(f"Blok Boyutu     : {bs} byte\n")
            log.write(f"Toplam Byte     : {total_bytes}\n")
            log.write(f"Toplam Blok     : {num_blocks}\n")
            log.write("====================================\n\n")
        except Exception as e:
            sys.exit(f"❌ Log dosyası oluşturulamadı: {e}")

    out_lines = []

    # Blok bazında işleme
    for i in range(0, total_bytes, bs):
        block = data[i:i+bs]
        reversed_block = block[::-1]
        hex_str = reversed_block.hex()

        out_lines.append(hex_str)

        # Log kaydı
        if log:
            log.write(f"[Block @ 0x{i:08X}]\n")
            log.write(f"  Original : {block.hex()}\n")
            log.write(f"  Reversed : {reversed_block.hex()}\n")
            log.write(f"  HEX line : {hex_str}\n\n")

    # HEX dosyasına yaz
    try:
        outfile.write_text("\n".join(out_lines) + "\n")
    except Exception as e:
        sys.exit(f"❌ HEX dosyası yazılamadı: {e}")

    if log:
        log.write("=== Tamamlandı ===\n")
        log.close()

    print(f"✅ HEX üretildi: {outfile}")
    if logf:
        print(f"📄 Log dosyası: {logf}")

if __name__ == "__main__":
    main()
