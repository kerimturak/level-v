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


def build_programmer_payload(words: list[int]) -> bytes:
    """
    Exact byte stream sent to FPGA / ram_programmer (magic + big-endian count +
    little-endian words). Use with Verilator +PROG_UART_PAYLOAD=<file>.
    """
    word_count = len(words)
    count_bytes = struct.pack(">I", word_count)
    body = b"".join(struct.pack("<I", w & 0xFFFFFFFF) for w in words)
    return MAGIC_SEQUENCE + count_bytes + body


# ─────────────────────────────────────────────────────────────────────────────
# UART programming
# ─────────────────────────────────────────────────────────────────────────────
def program_fpga(
    port: str,
    baud: int,
    words: list[int],
    verbose: bool = False,
    inter_byte_delay_s: float = 0.0,
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

    print(f"╔══════════════════════════════════════════════════╗")
    print(f"║       Level RISC-V — FPGA UART Programmer       ║")
    print(f"╠══════════════════════════════════════════════════╣")
    print(f"║  Port       : {port:<35s}║")
    print(f"║  Baud Rate  : {baud:<35d}║")
    print(f"║  Word Count : {word_count:<35d}║")
    print(f"║  Total Bytes: {total_bytes:<35d}║")
    print(f"╚══════════════════════════════════════════════════╝")

    # Seconds: enough for wire-time at baud + margin (large .mem can be slow to push).
    est_wire_s = (max(total_bytes, 64) * 12.0) / float(max(baud, 1))
    write_timeout_s = max(60.0, est_wire_s * 2.0)

    try:
        # dsrdtr=False: many USB-UART bridges tie DTR/RTS to EN/RST — toggling can reset the FPGA.
        ser = serial.Serial(
            port,
            baud,
            timeout=2,
            write_timeout=write_timeout_s,
            rtscts=False,
            dsrdtr=False,
        )
    except serial.SerialException as e:
        print(f"\n✗ Could not open UART: {e}")
        if "No such file" in str(e):
            print("\n  If you use WSL:")
            print("  1. On Windows: usbipd list")
            print("  2. On Windows: usbipd bind --busid <BUSID>")
            print("  3. On Windows: usbipd attach --wsl --busid <BUSID>")
            print("  4. In WSL:     ls /dev/ttyUSB* /dev/ttyACM*")
            print(f"  5. Or use: --port /dev/ttyS8  (for COM8)")
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
        time.sleep(0.05)  # let adapter / FPGA RX line settle after open
        try:
            ser.reset_input_buffer()
        except (AttributeError, serial.SerialException):
            pass

        # ── Step 1: Magic sequence ──
        print(f"\n[1/3] Sending magic sequence: {MAGIC_SEQUENCE.decode()}")
        write_bytes(MAGIC_SEQUENCE)
        time.sleep(0.02)

        # ── Step 2: Word count (big-endian) ──
        count_bytes = struct.pack(">I", word_count)  # big-endian uint32
        print(f"[2/3] Sending word count: {word_count} (0x{word_count:08x})")
        write_bytes(count_bytes)
        time.sleep(0.02)

        # ── Step 3: Data words (little-endian) ──
        print(f"[3/3] Sending program data ({word_count} words)...")

        # Progress milestones
        milestone = max(1, word_count // 10)
        start_time = time.time()

        for i, word in enumerate(words):
            # Little-endian: LSB first (ram_programmer.sv shift-right assembly)
            word_bytes = struct.pack("<I", word)
            write_bytes(word_bytes)

            if verbose and i < 16:
                print(f"  [{i:6d}] 0x{word:08x} → {word_bytes.hex()}")

            # Progress
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
        print(f"  ✓ Programming complete!")
        print(f"    Time : {elapsed:.2f}s")
        print(f"    Rate : {rate:.0f} B/s ({rate/1024:.1f} KB/s)")
        print(f"══════════════════════════════════════════════════")
        return True

    except serial.SerialException as e:
        print(f"\n✗ UART communication error: {e}")
        return False
    finally:
        ser.close()


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

    args = parser.parse_args()

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
    print(f"Source: {rel_path}")

    # ── Load and send ──
    words = load_mem_file(mem_path)
    if not words:
        print(f"✗ File empty or unreadable: {mem_path}")
        sys.exit(1)

    print(f"Loaded: {len(words)} word(s) ({len(words)*4} byte(s))\n")

    if args.dump_payload:
        blob = build_programmer_payload(words)
        out_path = os.path.abspath(args.dump_payload)
        with open(out_path, "wb") as f:
            f.write(blob)
        print(f"Wrote programmer payload: {len(blob)} byte(s) → {out_path}")
        sys.exit(0)

    success = program_fpga(
        args.port,
        args.baud,
        words,
        verbose=args.verbose,
        inter_byte_delay_s=args.inter_byte_delay,
    )
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
