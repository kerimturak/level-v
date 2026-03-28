#!/usr/bin/env python3
"""
Level RISC-V — FPGA UART Programmer
====================================
Loads a program into the Level RISC-V core on the FPGA over UART from the host.

Protocol (matches ram_programmer.sv):
  1. Send magic sequence: "LEVELTEST" (9-byte ASCII)
  2. Send word count: 4 bytes big-endian
  3. Send data words: each 4 bytes little-endian
  4. RTL transitions to ST_FINISH automatically (no extra signal needed)

Usage:
  # Auto-locate .mem from the build system:
  python3 uart_send_data.py --test rv32ui-p-add

  # Specify .mem path directly:
  python3 uart_send_data.py --mem path/to/test.mem

  # Load CoreMark / Dhrystone / Embench (paths are searched under build/tests/):
  python3 uart_send_data.py --test coremark
  python3 uart_send_data.py --test dhrystone
  python3 uart_send_data.py --test crc32

  # Set port and baud (WSL: COM8 ≈ /dev/ttyS8; native Windows: COM8):
  python3 uart_send_data.py --test rv32ui-p-add --port /dev/ttyS8 --baud 115200

Troubleshooting:
  • Bitstream must use the same PROG_BAUD_RATE (115200) and CPU_CLK / UART divider as rtl/pkg/level_param.sv.
  • If the board resets when you run the script, try another USB cable/port or disable adapter auto-reset.
  • If magic is ignored: wrong UART pin, wrong baud, or garbage in RX — script clears RX buffer after open.
  • If transfer hangs: increase write timeout is automatic; try --inter-byte-delay 0.00005 for very marginal links.

  # Via Makefile:
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
    print("ERROR: pyserial is required. Install with: pip install pyserial")
    sys.exit(1)

# ─────────────────────────────────────────────────────────────────────────────
# Constants (aligned with level_param.sv)
# ─────────────────────────────────────────────────────────────────────────────
MAGIC_SEQUENCE = b"LEVELTEST"       # ram_programmer.sv: PROGRAM_SEQUENCE
DEFAULT_BAUD   = 115200             # ram_programmer.sv: PROG_BAUD_RATE
DEFAULT_PORT   = "/dev/ttyS8"      # WSL: COM8 → /dev/ttyS8

# Project root (script/python/fpga/ → three levels up)
SCRIPT_DIR   = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.abspath(os.path.join(SCRIPT_DIR, "..", "..", ".."))
BUILD_DIR    = os.path.join(PROJECT_ROOT, "build", "tests")


# ─────────────────────────────────────────────────────────────────────────────
# Find .mem file
# ─────────────────────────────────────────────────────────────────────────────
def find_mem_file(test_name: str) -> str:
    """
    Find the .mem file for a test name under the build directory.

    Search order:
      build/tests/riscv-tests/mem/<test>.mem
      build/tests/riscv-arch-test/mem/<test>.mem
      build/tests/imperas/mem/<test>.mem
      build/tests/coremark/<test>.mem
      build/tests/custom/<test>.mem
      build/tests/**/mem/<test>.mem   (generic glob)
    """
    search_patterns = [
        os.path.join(BUILD_DIR, "riscv-tests", "mem", f"{test_name}.mem"),
        os.path.join(BUILD_DIR, "riscv-arch-test", "mem", f"{test_name}.mem"),
        os.path.join(BUILD_DIR, "imperas", "mem", f"{test_name}.mem"),
        os.path.join(BUILD_DIR, "coremark", f"{test_name}.mem"),
        os.path.join(BUILD_DIR, "dhrystone", f"{test_name}.mem"),
        os.path.join(BUILD_DIR, "embench", "mem", f"{test_name}.mem"),
        os.path.join(BUILD_DIR, "torture", "mem", f"{test_name}.mem"),
        os.path.join(BUILD_DIR, "riscv-benchmarks", "mem", f"{test_name}.mem"),
        os.path.join(BUILD_DIR, "custom", f"{test_name}.mem"),
    ]

    for path in search_patterns:
        if os.path.isfile(path):
            return path

    # Glob fallback
    matches = glob.glob(os.path.join(BUILD_DIR, "**", f"{test_name}.mem"), recursive=True)
    if matches:
        return matches[0]

    # Also search project root (e.g. coremark.mem)
    root_file = os.path.join(PROJECT_ROOT, f"{test_name}.mem")
    if os.path.isfile(root_file):
        return root_file

    return None


# ─────────────────────────────────────────────────────────────────────────────
# Read .mem file
# ─────────────────────────────────────────────────────────────────────────────
def load_mem_file(filepath: str) -> list[int]:
    """
    Read a .mem file and return a list of 32-bit words.
    Format: one 32-bit hex word per line (e.g. 0500006f)
    Blank lines and comments (//) are skipped.
    """
    words = []
    with open(filepath, "r") as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            # Skip blank lines and comments
            if not line or line.startswith("//") or line.startswith("#"):
                continue
            # Skip @ address lines (Verilog $readmemh format)
            if line.startswith("@"):
                continue
            # First hex token only (allows "deadbeef // comment" or tab-separated)
            line = line.split()[0] if line.split() else ""
            if not line:
                continue
            try:
                word = int(line, 16)
                words.append(word & 0xFFFFFFFF)
            except ValueError:
                print(f"  WARNING: Skipped line {line_num} (invalid hex): '{line}'")
    return words


def _p(msg: str, *, quiet: bool, flush: bool = True) -> None:
    if not quiet:
        print(msg, flush=flush)


def build_programmer_payload(words: list[int]) -> bytes:
    """
    Exact byte stream sent to FPGA / ram_programmer (magic + big-endian count +
    little-endian words). Use with Verilator +PROG_UART_PAYLOAD=<file>.
    """
    word_count = len(words)
    count_bytes = struct.pack(">I", word_count)
    body = b"".join(struct.pack("<I", w & 0xFFFFFFFF) for w in words)
    return MAGIC_SEQUENCE + count_bytes + body


def _hexdump_region(data: bytes, start: int, end: int, width: int = 16) -> None:
    end = min(end, len(data))
    for i in range(start, end, width):
        chunk = data[i : min(i + width, end)]
        hx = " ".join(f"{b:02x}" for b in chunk)
        asc = "".join(chr(b) if 32 <= b < 127 else "." for b in chunk)
        print(f"  {i:08x}  {hx:<{max(1, width * 3 - 1)}} |{asc}", flush=True)


def print_sent_program_hex(
    data: bytes,
    *,
    full: bool,
    head_bytes: int = 128,
    tail_bytes: int = 64,
) -> None:
    """Print exact UART wire bytes (for logs / cross-check with --dump-payload)."""
    n = len(data)
    print(f"\n--- Gönderilen program (tam kablo: {n} B) — hex ---", flush=True)
    if full or n <= head_bytes + tail_bytes:
        _hexdump_region(data, 0, n)
        return
    _hexdump_region(data, 0, head_bytes)
    skipped = n - head_bytes - tail_bytes
    print(
        f"  --------  … {skipped} byte atlandı — tam döküm: --full-payload-hex …",
        flush=True,
    )
    _hexdump_region(data, n - tail_bytes, n)


# ─────────────────────────────────────────────────────────────────────────────
# UART programming
# ─────────────────────────────────────────────────────────────────────────────
def program_fpga(
    port: str,
    baud: int,
    words: list[int],
    verbose: bool = False,
    inter_byte_delay_s: float = 0.0,
    quiet: bool = False,
    show_payload_hex: bool = True,
    full_payload_hex: bool = False,
) -> bool:
    """
    Load the FPGA over UART using the ram_programmer.sv protocol.

    Protocol:
      1. Send MAGIC_SEQUENCE ("LEVELTEST", 9 bytes)
      2. Send word count (4 bytes, big-endian)
      3. Send each word (4 bytes, little-endian — RISC-V byte order)
    """
    word_count = len(words)
    total_bytes = len(MAGIC_SEQUENCE) + 4 + (word_count * 4)
    step_hi = 7

    _p(f"╔══════════════════════════════════════════════════╗", quiet=quiet)
    _p(f"║       Level RISC-V — FPGA UART Programmer       ║", quiet=quiet)
    _p(f"╠══════════════════════════════════════════════════╣", quiet=quiet)
    _p(f"║  Port        : {port:<34s}║", quiet=quiet)
    _p(f"║  Baud        : {baud:<34d}║", quiet=quiet)
    _p(f"║  Word count  : {word_count:<34d}║", quiet=quiet)
    _p(f"║  Wire bytes  : {total_bytes:<34d}║", quiet=quiet)
    if inter_byte_delay_s > 0:
        _p(f"║  Inter-byte  : {inter_byte_delay_s:<34g}s║", quiet=quiet)
    _p(f"╚══════════════════════════════════════════════════╝", quiet=quiet)

    est_wire_s = (max(total_bytes, 64) * 12.0) / float(max(baud, 1))
    write_timeout_s = max(60.0, est_wire_s * 2.0)
    _p(f"\n>>> [1/{step_hi}] Özet: kabloda ~{est_wire_s:.1f}s tahmini; "
        f"write_timeout={write_timeout_s:.0f}s", quiet=quiet)

    try:
        _p(f">>> [2/{step_hi}] Seri port açılıyor: {port!r} …", quiet=quiet)
        ser = serial.Serial(
            port,
            baud,
            timeout=2,
            write_timeout=write_timeout_s,
            rtscts=False,
            dsrdtr=False,
        )
        _p(f"    OK — port açık (dsrdtr/rtscts kapalı)", quiet=quiet)
    except serial.SerialException as e:
        print(f"\n✗ [2/{step_hi}] Port açılamadı: {e}", flush=True)
        if "No such file" in str(e):
            print("\n  WSL kullanıyorsan COM yerine /dev/ttyUSB0 vb. kullan; ya da Windows’ta py ile çalıştır:")
            print("  1. Windows: usbipd list / attach --wsl")
            print("  2. WSL: ls /dev/ttyUSB* /dev/ttyACM*")
        return False

    def write_bytes(data: bytes) -> None:
        if inter_byte_delay_s and inter_byte_delay_s > 0:
            for b in data:
                ser.write(bytes([b]))
                ser.flush()
                time.sleep(inter_byte_delay_s)
        else:
            ser.write(data)
            ser.flush()

    try:
        _p(f">>> [3/{step_hi}] Hat oturması 50ms, RX buffer temizleniyor…", quiet=quiet)
        time.sleep(0.05)
        try:
            ser.reset_input_buffer()
            _p("    OK — reset_input_buffer()", quiet=quiet)
        except (AttributeError, serial.SerialException) as ex:
            _p(f"    (atlandı: {ex})", quiet=quiet)

        sent = 0
        _p(f">>> [4/{step_hi}] Magic gönderiliyor ({len(MAGIC_SEQUENCE)} B): "
            f"{MAGIC_SEQUENCE.decode()!r}", quiet=quiet)
        write_bytes(MAGIC_SEQUENCE)
        sent += len(MAGIC_SEQUENCE)
        time.sleep(0.02)
        _p(f"    OK — şimdiye kadar toplam {sent} B (magic)", quiet=quiet)

        count_bytes = struct.pack(">I", word_count)
        _p(f">>> [5/{step_hi}] Kelime sayısı (4 B, big-endian): {word_count} "
            f"(hex BE: {count_bytes.hex()})", quiet=quiet)
        write_bytes(count_bytes)
        sent += 4
        time.sleep(0.02)
        _p(f"    OK — toplam {sent} B (magic+sayı)", quiet=quiet)

        payload_bytes = word_count * 4
        _p(f">>> [6/{step_hi}] Yük gövdesi: {word_count} kelime = {payload_bytes} B (little-endian / kelime)…",
            quiet=quiet)
        if word_count > 0:
            _p(f"    İlk kelime: 0x{words[0]:08x} | Son kelime: 0x{words[-1]:08x}", quiet=quiet)

        milestone = max(1, word_count // 10)
        start_time = time.time()

        for i, word in enumerate(words):
            word_bytes = struct.pack("<I", word)
            write_bytes(word_bytes)
            sent += 4

            if verbose and i < 16:
                print(f"  [{i:6d}] 0x{word:08x} → {word_bytes.hex()}", flush=True)

            if (i + 1) % milestone == 0 or (i + 1) == word_count:
                pct = (i + 1) * 100 // word_count if word_count else 100
                elapsed = time.time() - start_time
                rate = (i + 1) * 4 / elapsed if elapsed > 0 else 0
                _p(f"    … {pct}% ({i+1}/{word_count}) {elapsed:.1f}s ~{rate:.0f} B/s — gönderilen {sent} B",
                    quiet=quiet)

        ser.flush()
        elapsed = time.time() - start_time
        rate = total_bytes / elapsed if elapsed > 0 else 0

        wire = build_programmer_payload(words)
        if len(wire) != sent:
            print(
                f"✗ İç tutarsızlık: beklenen kablo {len(wire)} B, sayaç {sent} B",
                flush=True,
            )
        if show_payload_hex and not quiet:
            print_sent_program_hex(wire, full=full_payload_hex)

        _p(f"\n>>> [7/{step_hi}] Bitti: port kapatılıyor", quiet=quiet)
        print(f"══════════════════════════════════════════════════", flush=True)
        print(f"  ✓ Gönderim tamam (RAM programlayıcı protokolü)", flush=True)
        print(f"    Süre : {elapsed:.2f}s", flush=True)
        print(f"    Hız  : {rate:.0f} B/s ({rate/1024:.1f} KB/s)", flush=True)
        print(f"    Toplam kablo: {sent} B (beklenen: {total_bytes} B)", flush=True)
        print(f"══════════════════════════════════════════════════", flush=True)
        if sent != total_bytes:
            print(f"✗ Uyarı: byte sayısı beklenenden farklı ({sent} vs {total_bytes})", flush=True)
        return True

    except serial.SerialException as e:
        print(f"\n✗ [UART] İletişim hatası: {e}", flush=True)
        return False
    finally:
        ser.close()
        _p("    Port kapandı.", quiet=quiet)


# ─────────────────────────────────────────────────────────────────────────────
# List available tests
# ─────────────────────────────────────────────────────────────────────────────
def list_available_tests():
    """List .mem files found under the build directory."""
    print("Available .mem files:")
    print("=" * 60)

    mem_files = glob.glob(os.path.join(BUILD_DIR, "**", "*.mem"), recursive=True)
    root_mems = glob.glob(os.path.join(PROJECT_ROOT, "*.mem"))
    all_files = sorted(mem_files + root_mems)

    if not all_files:
        print("  (None yet — run 'make isa' or 'make coremark' first)")
        return

    for f in all_files:
        rel = os.path.relpath(f, PROJECT_ROOT)
        name = os.path.splitext(os.path.basename(f))[0]
        print(f"  {name:<30s}  {rel}")

    print(f"\nTotal: {len(all_files)} file(s)")


# ─────────────────────────────────────────────────────────────────────────────
# Main entry
# ─────────────────────────────────────────────────────────────────────────────
def main():
    parser = argparse.ArgumentParser(
        description="Level RISC-V — FPGA UART Programmer",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --test rv32ui-p-add                        # Load ISA test
  %(prog)s --test coremark                            # Load CoreMark
  %(prog)s --mem build/tests/custom/my_test.mem       # Custom .mem file
  %(prog)s --test rv32ui-p-add --port COM8            # Windows port
  %(prog)s --test rv32ui-p-add --port /dev/ttyUSB1    # Different Linux port
  %(prog)s --test rv32ui-p-add --dump-payload prog.bin
  # Verilator: first arg = max cycles; omit +INIT_FILE to RAM-only via UART
  #   ./Vlevel_wrapper 8000000 +PROG_UART_PAYLOAD=prog.bin +uart_log_path=out.log
  %(prog)s --list                                     # List available tests

Makefile integration:
  make fpga_program T=rv32ui-p-add
  make fpga_program T=coremark PORT=/dev/ttyUSB0
        """,
    )

    # Input source (one required)
    input_group = parser.add_mutually_exclusive_group()
    input_group.add_argument(
        "--test", "-t",
        help="Test name (.mem is searched under build/)",
    )
    input_group.add_argument(
        "--mem", "-m",
        help="Path to .mem file",
    )
    input_group.add_argument(
        "--list", "-l",
        action="store_true",
        help="List available .mem files",
    )

    # UART settings
    parser.add_argument(
        "--port", "-p",
        default=os.environ.get("FPGA_PORT", DEFAULT_PORT),
        help=f"Serial port (default: {DEFAULT_PORT}, override with FPGA_PORT env)",
    )
    parser.add_argument(
        "--baud", "-b",
        type=int,
        default=int(os.environ.get("FPGA_BAUD", DEFAULT_BAUD)),
        help=f"Baud rate (default: {DEFAULT_BAUD})",
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Print first 16 words in detail",
    )
    parser.add_argument(
        "--quiet", "-q",
        action="store_true",
        help="Less console output (only banner + final result / errors)",
    )
    parser.add_argument(
        "--inter-byte-delay",
        type=float,
        default=float(os.environ.get("FPGA_UART_INTER_BYTE_DELAY", "0")),
        metavar="SEC",
        help="Optional delay between each byte (e.g. 0.0001 if programming fails; default 0)",
    )
    parser.add_argument(
        "--dump-payload",
        metavar="PATH",
        help="Write raw programmer stream to PATH for sim (+PROG_UART_PAYLOAD); no serial",
    )
    parser.add_argument(
        "--no-show-payload",
        action="store_true",
        help="Do not print sent wire bytes as hex after transfer",
    )
    parser.add_argument(
        "--full-payload-hex",
        action="store_true",
        help="Print every byte on the wire as hex (default: first 128 + last 64 B only)",
    )

    args = parser.parse_args()
    quiet = args.quiet or os.environ.get("FPGA_UART_QUIET", "") == "1"

    # ── List mode ──
    if args.list:
        list_available_tests()
        return

    # ── Resolve .mem path ──
    if args.mem:
        mem_path = args.mem
        if not os.path.isfile(mem_path):
            print(f"✗ File not found: {mem_path}")
            sys.exit(1)
    elif args.test:
        mem_path = find_mem_file(args.test)
        if not mem_path:
            print(f"✗ No .mem file found for '{args.test}'.")
            print(f"  Build first: make run T={args.test}")
            print(f"  or: make isa / make arch / make coremark")
            sys.exit(1)
    else:
        parser.print_help()
        print("\n✗ Specify --test or --mem.")
        sys.exit(1)

    # ── File info ──
    mem_path = os.path.abspath(mem_path)
    rel_path = os.path.relpath(mem_path, PROJECT_ROOT)
    _p(f"\n>>> [0a] Kaynak: {rel_path}", quiet=quiet)

    # ── Load and send ──
    _p(f">>> [0b] .mem okunuyor…", quiet=quiet)
    words = load_mem_file(mem_path)
    if not words:
        print(f"✗ File empty or unreadable: {mem_path}")
        sys.exit(1)

    _p(f"    OK — {len(words)} kelime ({len(words)*4} B data)\n", quiet=quiet)

    if args.dump_payload:
        _p(">>> [dump] Binary payload yazılıyor…", quiet=quiet)
        blob = build_programmer_payload(words)
        out_path = os.path.abspath(args.dump_payload)
        with open(out_path, "wb") as f:
            f.write(blob)
        print(f"OK — {len(blob)} B → {out_path}", flush=True)
        sys.exit(0)

    success = program_fpga(
        args.port,
        args.baud,
        words,
        verbose=args.verbose,
        inter_byte_delay_s=args.inter_byte_delay,
        quiet=quiet,
        show_payload_hex=not args.no_show_payload,
        full_payload_hex=args.full_payload_hex,
    )
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
