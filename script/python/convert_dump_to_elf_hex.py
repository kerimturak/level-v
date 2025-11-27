"""
dump_to_elf_hex.py — CERES RISC-V Test Pipeline Conversion Tool

This utility converts a RISC-V .dump file (raw assembly dump produced by
riscv-tests or other generators) into:

    1) A runnable ELF binary (.elf)
    2) A Verilog-compatible memory initialization file (.hex)

The script performs two main steps:
    • Invokes the RISC-V GCC toolchain to assemble and link the .dump file
      into a proper ELF using the Ceres bare-metal environment (env/p, link.ld).
    • Converts the generated ELF into a Verilog HEX file using objcopy,
      enabling direct loading into FPGA/Verilator/SoC simulation memories.

This tool is used inside the CERES build pipeline to automatically transform
ISA/Benchmark outputs into loadable artifacts for hardware and simulation
environments.

Usage:
    python dump_to_elf_hex.py <file.dump>

Requirements:
    • RISC-V GNU toolchain (riscv64-unknown-elf-*)
    • Ceres environment & linker script (env/p/link.ld)
"""

import sys
import os
import subprocess

RISCV_PREFIX = "riscv64-unknown-elf-"
RISCV_GCC = f"{RISCV_PREFIX}gcc"
RISCV_OBJCOPY = f"{RISCV_PREFIX}objcopy"

def convert_dump_to_elf_hex(dump_file):
    base_name = dump_file.replace(".dump", "")
    elf_file = f"{base_name}.elf"
    hex_file = f"{base_name}.hex"

    # Check if .dump file exists
    if not os.path.exists(dump_file):
        print(f"Error: {dump_file} not found!")
        sys.exit(1)

    # Compile ELF
    elf_cmd = [
        RISCV_GCC, "-static", "-mcmodel=medany", "-fvisibility=hidden",
        "-nostdlib", "-nostartfiles",
        "-I../env/p", "-I./macros/scalar", "-T../env/p/link.ld",
        dump_file, "-o", elf_file
    ]
    
    try:
        subprocess.run(elf_cmd, check=True)
        print(f"✅ Created ELF: {elf_file}")
    except subprocess.CalledProcessError as e:
        print(f"❌ Failed to create ELF: {e}")
        sys.exit(1)

    # Convert ELF to HEX
    hex_cmd = [RISCV_OBJCOPY, "-O", "verilog", elf_file, hex_file]
    
    try:
        subprocess.run(hex_cmd, check=True)
        print(f"✅ Created HEX: {hex_file}")
    except subprocess.CalledProcessError as e:
        print(f"❌ Failed to create HEX: {e}")
        sys.exit(1)

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python dump_to_elf_hex.py <file.dump>")
        sys.exit(1)
    
    dump_file = sys.argv[1]
    convert_dump_to_elf_hex(dump_file)
