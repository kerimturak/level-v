#!/usr/bin/env python3
"""
CERES RISC-V — FPGA UART Programmer
====================================
Bilgisayar üzerinden FPGA'de yüklü olan CERES işlemciye UART ile program yükler.

Protokol (ram_programmer.sv ile uyumlu):
  1. Magic sequence gönder: "CERESTEST" (9 byte ASCII)
  2. Word sayısını gönder: 4 byte big-endian
  3. Data word'lerini gönder: her biri 4 byte little-endian
  4. RTL otomatik olarak ST_FINISH'e geçer (ek sinyal gerekmez)

Kullanım:
  # Build sisteminden .mem dosyasını otomatik bul:
  python3 uart_send_data.py --test rv32ui-p-add

  # Doğrudan .mem dosyası belirt:
  python3 uart_send_data.py --mem path/to/test.mem

  # CoreMark yükle:
  python3 uart_send_data.py --test coremark

  # Port ve baud rate ayarla (WSL'de COM8 = /dev/ttyS8):
  python3 uart_send_data.py --test rv32ui-p-add --port /dev/ttyS8 --baud 115200

  # Makefile ile:
  make fpga_program T=rv32ui-p-add
"""

import argparse
import os
import sys
import glob
import struct
import time

try:
    import serial
except ImportError:
    print("HATA: pyserial paketi gerekli. Kurulum: pip install pyserial")
    sys.exit(1)

# ─────────────────────────────────────────────────────────────────────────────
# Sabitler (ceres_param.sv ile uyumlu)
# ─────────────────────────────────────────────────────────────────────────────
MAGIC_SEQUENCE = b"CERESTEST"       # ram_programmer.sv: PROGRAM_SEQUENCE
DEFAULT_BAUD   = 115200             # ram_programmer.sv: PROG_BAUD_RATE
DEFAULT_PORT   = "/dev/ttyS8"      # WSL: COM8 → /dev/ttyS8

# Proje kök dizini (script/python/fpga/ → 3 seviye yukarı)
SCRIPT_DIR   = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.abspath(os.path.join(SCRIPT_DIR, "..", "..", ".."))
BUILD_DIR    = os.path.join(PROJECT_ROOT, "build", "tests")


# ─────────────────────────────────────────────────────────────────────────────
# .mem Dosya Arama
# ─────────────────────────────────────────────────────────────────────────────
def find_mem_file(test_name: str) -> str:
    """
    Build dizininde test adına göre .mem dosyasını bulur.
    Arama sırası:
      build/tests/riscv-tests/mem/<test>.mem
      build/tests/riscv-arch-test/mem/<test>.mem
      build/tests/imperas/mem/<test>.mem
      build/tests/coremark/<test>.mem
      build/tests/custom/<test>.mem
      build/tests/**/mem/<test>.mem   (genel glob)
    """
    search_patterns = [
        os.path.join(BUILD_DIR, "riscv-tests", "mem", f"{test_name}.mem"),
        os.path.join(BUILD_DIR, "riscv-arch-test", "mem", f"{test_name}.mem"),
        os.path.join(BUILD_DIR, "imperas", "mem", f"{test_name}.mem"),
        os.path.join(BUILD_DIR, "coremark", f"{test_name}.mem"),
        os.path.join(BUILD_DIR, "custom", f"{test_name}.mem"),
    ]

    for path in search_patterns:
        if os.path.isfile(path):
            return path

    # Glob fallback
    matches = glob.glob(os.path.join(BUILD_DIR, "**", f"{test_name}.mem"), recursive=True)
    if matches:
        return matches[0]

    # Proje kökünde de ara (coremark.mem gibi)
    root_file = os.path.join(PROJECT_ROOT, f"{test_name}.mem")
    if os.path.isfile(root_file):
        return root_file

    return None


# ─────────────────────────────────────────────────────────────────────────────
# .mem Dosya Okuma
# ─────────────────────────────────────────────────────────────────────────────
def load_mem_file(filepath: str) -> list[int]:
    """
    .mem dosyasını okur ve 32-bit word listesi döner.
    Format: Her satırda bir 32-bit hex word (örn: 0500006f)
    Boş satırlar ve yorumlar (//) atlanır.
    """
    words = []
    with open(filepath, "r") as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            # Boş satır veya yorum atla
            if not line or line.startswith("//") or line.startswith("#"):
                continue
            # @ ile başlayan adres satırlarını atla (verilog $readmemh formatı)
            if line.startswith("@"):
                continue
            try:
                word = int(line, 16)
                words.append(word & 0xFFFFFFFF)
            except ValueError:
                print(f"  UYARI: Satır {line_num} atlandı (geçersiz hex): '{line}'")
    return words


# ─────────────────────────────────────────────────────────────────────────────
# UART Programlama
# ─────────────────────────────────────────────────────────────────────────────
def program_fpga(port: str, baud: int, words: list[int], verbose: bool = False) -> bool:
    """
    ram_programmer.sv protokolüne göre UART üzerinden FPGA'ye program yükler.

    Protokol:
      1. MAGIC_SEQUENCE gönder ("CERESTEST", 9 byte)
      2. Word sayısını gönder (4 byte, big-endian)
      3. Her word'ü gönder (4 byte, little-endian — RISC-V byte order)
    """
    word_count = len(words)
    total_bytes = len(MAGIC_SEQUENCE) + 4 + (word_count * 4)

    print(f"╔══════════════════════════════════════════════════╗")
    print(f"║       CERES RISC-V — FPGA UART Programmer       ║")
    print(f"╠══════════════════════════════════════════════════╣")
    print(f"║  Port       : {port:<35s}║")
    print(f"║  Baud Rate  : {baud:<35d}║")
    print(f"║  Word Count : {word_count:<35d}║")
    print(f"║  Total Bytes: {total_bytes:<35d}║")
    print(f"╚══════════════════════════════════════════════════╝")

    try:
        ser = serial.Serial(port, baud, timeout=2)
    except serial.SerialException as e:
        print(f"\n✗ UART açılamadı: {e}")
        if "No such file" in str(e):
            print("\n  WSL kullanıyorsanız:")
            print("  1. Windows'ta: usbipd list")
            print("  2. Windows'ta: usbipd bind --busid <BUSID>")
            print("  3. Windows'ta: usbipd attach --wsl --busid <BUSID>")
            print("  4. WSL'de:     ls /dev/ttyUSB* /dev/ttyACM*")
            print(f"  5. Veya doğrudan: --port /dev/ttyS8  (COM8 için)")
        return False

    try:
        # ── Adım 1: Magic Sequence ──
        print(f"\n[1/3] Magic sequence gönderiliyor: {MAGIC_SEQUENCE.decode()}")
        ser.write(MAGIC_SEQUENCE)
        ser.flush()
        time.sleep(0.01)

        # ── Adım 2: Word Count (big-endian) ──
        count_bytes = struct.pack(">I", word_count)  # big-endian uint32
        print(f"[2/3] Word sayısı gönderiliyor: {word_count} (0x{word_count:08x})")
        ser.write(count_bytes)
        ser.flush()
        time.sleep(0.01)

        # ── Adım 3: Data Words (little-endian) ──
        print(f"[3/3] Program verisi gönderiliyor ({word_count} word)...")

        # İlerleme çubuğu için
        milestone = max(1, word_count // 10)
        start_time = time.time()

        for i, word in enumerate(words):
            # Little-endian: LSB first (ram_programmer.sv shift-right assembly)
            word_bytes = struct.pack("<I", word)
            ser.write(word_bytes)

            if verbose and i < 16:
                print(f"  [{i:6d}] 0x{word:08x} → {word_bytes.hex()}")

            # İlerleme göster
            if (i + 1) % milestone == 0:
                pct = (i + 1) * 100 // word_count
                elapsed = time.time() - start_time
                rate = (i + 1) * 4 / elapsed if elapsed > 0 else 0
                print(f"  ▓ {pct:3d}%  ({i+1}/{word_count})  "
                      f"{elapsed:.1f}s  {rate:.0f} B/s")

        ser.flush()
        elapsed = time.time() - start_time
        rate = total_bytes / elapsed if elapsed > 0 else 0

        print(f"\n══════════════════════════════════════════════════")
        print(f"  ✓ Programlama tamamlandı!")
        print(f"    Süre : {elapsed:.2f}s")
        print(f"    Hız  : {rate:.0f} B/s ({rate/1024:.1f} KB/s)")
        print(f"══════════════════════════════════════════════════")
        return True

    except serial.SerialException as e:
        print(f"\n✗ UART iletişim hatası: {e}")
        return False
    finally:
        ser.close()


# ─────────────────────────────────────────────────────────────────────────────
# Mevcut Testleri Listele
# ─────────────────────────────────────────────────────────────────────────────
def list_available_tests():
    """Build dizininde bulunan .mem dosyalarını listeler."""
    print("Mevcut .mem dosyaları:")
    print("=" * 60)

    mem_files = glob.glob(os.path.join(BUILD_DIR, "**", "*.mem"), recursive=True)
    root_mems = glob.glob(os.path.join(PROJECT_ROOT, "*.mem"))
    all_files = sorted(mem_files + root_mems)

    if not all_files:
        print("  (Henüz derlenmemiş — önce 'make isa' veya 'make coremark' çalıştırın)")
        return

    for f in all_files:
        rel = os.path.relpath(f, PROJECT_ROOT)
        name = os.path.splitext(os.path.basename(f))[0]
        print(f"  {name:<30s}  {rel}")

    print(f"\nToplam: {len(all_files)} dosya")


# ─────────────────────────────────────────────────────────────────────────────
# Ana Giriş
# ─────────────────────────────────────────────────────────────────────────────
def main():
    parser = argparse.ArgumentParser(
        description="CERES RISC-V — FPGA UART Programmer",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Örnekler:
  %(prog)s --test rv32ui-p-add                        # ISA testi yükle
  %(prog)s --test coremark                            # CoreMark yükle
  %(prog)s --mem build/tests/custom/my_test.mem       # Özel .mem dosyası
  %(prog)s --test rv32ui-p-add --port COM8            # Windows portu
  %(prog)s --test rv32ui-p-add --port /dev/ttyUSB1    # Farklı Linux portu
  %(prog)s --list                                     # Mevcut testleri listele

Makefile entegrasyonu:
  make fpga_program T=rv32ui-p-add
  make fpga_program T=coremark PORT=/dev/ttyUSB0
        """,
    )

    # Giriş kaynağı (biri zorunlu)
    input_group = parser.add_mutually_exclusive_group()
    input_group.add_argument(
        "--test", "-t",
        help="Test adı (build dizininde .mem dosyası aranır)",
    )
    input_group.add_argument(
        "--mem", "-m",
        help=".mem dosyasının yolu",
    )
    input_group.add_argument(
        "--list", "-l",
        action="store_true",
        help="Mevcut .mem dosyalarını listele",
    )

    # UART ayarları
    parser.add_argument(
        "--port", "-p",
        default=os.environ.get("FPGA_PORT", DEFAULT_PORT),
        help=f"Seri port (varsayılan: {DEFAULT_PORT}, FPGA_PORT env ile ayarlanır)",
    )
    parser.add_argument(
        "--baud", "-b",
        type=int,
        default=int(os.environ.get("FPGA_BAUD", DEFAULT_BAUD)),
        help=f"Baud rate (varsayılan: {DEFAULT_BAUD})",
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="İlk 16 word'ü detaylı göster",
    )

    args = parser.parse_args()

    # ── Liste modu ──
    if args.list:
        list_available_tests()
        return

    # ── .mem dosyası belirle ──
    if args.mem:
        mem_path = args.mem
        if not os.path.isfile(mem_path):
            print(f"✗ Dosya bulunamadı: {mem_path}")
            sys.exit(1)
    elif args.test:
        mem_path = find_mem_file(args.test)
        if not mem_path:
            print(f"✗ '{args.test}' için .mem dosyası bulunamadı.")
            print(f"  Önce derleme yapın: make run T={args.test}")
            print(f"  veya: make isa / make arch / make coremark")
            sys.exit(1)
    else:
        parser.print_help()
        print("\n✗ --test veya --mem belirtilmelidir.")
        sys.exit(1)

    # ── Dosya bilgisi ──
    mem_path = os.path.abspath(mem_path)
    rel_path = os.path.relpath(mem_path, PROJECT_ROOT)
    print(f"Kaynak: {rel_path}")

    # ── Yükle ve gönder ──
    words = load_mem_file(mem_path)
    if not words:
        print(f"✗ Dosya boş veya okunamadı: {mem_path}")
        sys.exit(1)

    print(f"Yüklenen: {len(words)} word ({len(words)*4} byte)\n")

    success = program_fpga(args.port, args.baud, words, verbose=args.verbose)
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()

