#!/usr/bin/env python3
"""
rules_isa_import
Unified ISA/BENCH import pipeline + integrated improved dump_parser
"""

import os, sys, glob, shutil, subprocess, argparse
from pathlib import Path
import re

# =============================================================================
# NAME NORMALIZER — remove .riscv suffix
# =============================================================================
def normalize_name(path):
    """Removes .riscv suffix from any filename."""
    name = os.path.basename(path)
    return name.replace(".riscv", "")

# =============================================================================
# SECTION 2 — Enhanced dump_parser
# =============================================================================

PASS_RE  = re.compile(r"^([0-9a-fA-F]+)\s+<pass>:$")
FAIL_RE  = re.compile(r"^([0-9a-fA-F]+)\s+<fail>:$")
HOST_RE  = re.compile(r"^([0-9a-fA-F]+)\s+<write_tohost>:$")
ADDR_RE  = re.compile(r"^([0-9a-fA-F]+)(?=(:|\s+<))")


def extract_pass_fail(dump_file: Path):
    """
    Dump dosyasından PASS / FAIL adreslerini çıkar.

    Öncelik:
      1) Açıkça tanımlı <pass> / <fail> label'ları
      2) Sadece <write_tohost> varsa → PASS = write_tohost, FAIL = PASS + 0x1000
      3) Hiçbiri yoksa → son görülen adres PASS, FAIL = PASS + 0x1000
    """
    pass_address      = None
    fail_address      = None
    write_tohost_addr = None
    last_address      = None

    with open(dump_file, "r") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue

            # 1) PASS
            m_pass = PASS_RE.match(line)
            if m_pass:
                pass_address = int(m_pass.group(1), 16)
                continue

            # 2) FAIL
            m_fail = FAIL_RE.match(line)
            if m_fail:
                fail_address = int(m_fail.group(1), 16)
                continue

            # 3) write_tohost
            m_host = HOST_RE.match(line)
            if m_host:
                write_tohost_addr = int(m_host.group(1), 16)
                continue

            # 4) Genel adres (fallback için)
            m_addr = ADDR_RE.match(line)
            if m_addr:
                last_address = int(m_addr.group(1), 16)

    # --- Öncelik 1: PASS / FAIL label'ları varsa her zaman bunları kullan ---
    if pass_address is not None or fail_address is not None:
        # Sadece birisi varsa, diğerini relative olarak tahmin et
        if pass_address is None and fail_address is not None:
            pass_address = fail_address - 0x1000
        if fail_address is None and pass_address is not None:
            fail_address = pass_address + 0x1000
        return pass_address, fail_address

    # --- Öncelik 2: Sadece write_tohost varsa ---
    if write_tohost_addr is not None:
        pass_address = write_tohost_addr
        fail_address = pass_address + 0x1000
        return pass_address, fail_address

    # --- Öncelik 3: Hiçbiri yoksa, son adres üzerinden tahmin ---
    if last_address is not None:
        pass_address = last_address
        fail_address = pass_address + 0x1000
        return pass_address, fail_address

    # Dump tamamen bozuksa:
    raise RuntimeError(f"No addresses found in dump: {dump_file}")


# =============================================================================
# SECTION 1 — ISA/BENCH PIPELINE
# =============================================================================

def run(cmd):
    print(f"  ➤ {' '.join(cmd)}")
    result = subprocess.run(cmd, check=False, capture_output=True, text=True)
    if result.returncode != 0:
        print(f"  ❌ ERROR: {result.stderr}")
        sys.exit(1)


def copy_if_newer(src, dst):
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    if not os.path.exists(dst) or os.path.getmtime(src) > os.path.getmtime(dst):
        shutil.copy2(src, dst)
        print(f"  📦 Copied: {os.path.basename(src)} → {dst}")
    else:
        print(f"  ↪ Skipped (up-to-date): {os.path.basename(src)}")


def process_test_group(name, src_dir, ceres_root):
    base_build = os.path.join(ceres_root, "build")
    group_root = os.path.join(base_build, f"tests/{name}")
    temp_root  = os.path.join(base_build, f"temp/{name}")
    logs_root  = os.path.join(base_build, "logs")

    elf_dst  = os.path.join(group_root, "elf")
    dump_dst = os.path.join(group_root, "dump")
    hex_dst  = os.path.join(group_root, "hex")
    mem_dst  = os.path.join(group_root, "mem")
    addr_dst = os.path.join(group_root, "pass_fail_addr")

    temp_elf  = os.path.join(temp_root, "elf")
    temp_dump = os.path.join(temp_root, "dump")

    hex_to_mem  = os.path.join(ceres_root, "script/python/makefile/hex_to_mem.py")
    objcopy = shutil.which("riscv32-unknown-elf-objcopy") or "riscv32-unknown-elf-objcopy"
    python  = shutil.which("python3")

    for d in [elf_dst, dump_dst, hex_dst, mem_dst, addr_dst, temp_elf, temp_dump, logs_root]:
        os.makedirs(d, exist_ok=True)

    print(f"\n🚀 Importing test group: {name}")
    print(f"   Source: {src_dir}")

    # Copy ELF
    src_elf_dir = os.path.join(src_dir, "elf")
    if os.path.isdir(src_elf_dir):
        print(f"\n📂 Copying ELF directory ...")
        for f in glob.glob(os.path.join(src_elf_dir, "*")):
            if os.path.isfile(f):
                dst = normalize_name(os.path.basename(f))
                copy_if_newer(f, os.path.join(elf_dst, dst))
    else:
        print(f"\n📄 No elf/ folder — scanning flat dir ...")
        for f in glob.glob(os.path.join(src_dir, "*")):
            if os.path.isfile(f) and not f.endswith(".dump"):
                dst = normalize_name(os.path.basename(f))
                copy_if_newer(f, os.path.join(elf_dst, dst))

    # Copy DUMP
    src_dump_dir = os.path.join(src_dir, "dump")
    if os.path.isdir(src_dump_dir):
        print(f"\n📂 Copying DUMP directory ...")
        for f in glob.glob(os.path.join(src_dump_dir, "*.dump")):
            dst = normalize_name(os.path.basename(f))
            copy_if_newer(f, os.path.join(dump_dst, dst))
    else:
        for f in glob.glob(os.path.join(src_dir, "*.dump")):
            dst = normalize_name(os.path.basename(f))
            copy_if_newer(f, os.path.join(dump_dst, dst))

    # Backup to temp/
    print(f"\n🧰 Backing up tests → temp/{name} ...")
    for f in glob.glob(os.path.join(elf_dst, "*")):
        copy_if_newer(f, os.path.join(temp_elf, os.path.basename(f)))
    for f in glob.glob(os.path.join(dump_dst, "*")):
        copy_if_newer(f, os.path.join(temp_dump, os.path.basename(f)))

    # Convert ELF → HEX → MEM
    print(f"\n🔧 Converting ELF → HEX → MEM + extracting PASS/FAIL ...\n")

    elf_files = [
        f for f in sorted(glob.glob(os.path.join(elf_dst, "*")))
        if os.path.isfile(f)
        and not f.endswith((".dump", ".log", ".txt", ".hex", ".mem", ".py", "Makefile"))
    ]

    for elf in elf_files:
        original = os.path.basename(elf)
        base = normalize_name(original)  # NORMALIZATION APPLIED

        hex_file  = os.path.join(hex_dst, f"{base}.hex")
        mem_file  = os.path.join(mem_dst, f"{base}.mem")
        dump_file = os.path.join(dump_dst, f"{base}.dump")

        run([objcopy, "-O", "verilog", elf, hex_file])
        run([python, hex_to_mem, hex_file, mem_file])

        if os.path.exists(dump_file):
            pass_addr, fail_addr = extract_pass_fail(Path(dump_file))

            out_file = os.path.join(addr_dst, f"{base}_addr.txt")
            with open(out_file, "w") as f:
                f.write(f"{hex(pass_addr)} {hex(fail_addr)}\n")
            print(f"  📝 PASS/FAIL → {out_file}")

    print(f"\n✅ Completed: {name}")
    print(f"   ELF  → {elf_dst}")
    print(f"   DUMP → {dump_dst}")
    print(f"   HEX  → {hex_dst}")
    print(f"   MEM  → {mem_dst}")
    print(f"   ADDR → {addr_dst}")
    print(f"   TEMP → {temp_root}")


# =============================================================================
# MAIN
# =============================================================================

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--isa-dir",  required=False, help="riscv-tests/isa dizini")
    ap.add_argument("--bench-dir", required=False, help="riscv-tests/benchmarks dizini")
    ap.add_argument("--ceres-root", required=True, help="Ceres-RISCV root")
    args = ap.parse_args()

    ceres_root = os.path.abspath(args.ceres_root)

    if not args.isa_dir and not args.bench_dir:
        print("❌ ERROR: Must provide --isa-dir or --bench-dir")
        sys.exit(1)

    if args.isa_dir:
        process_test_group("riscv-tests", os.path.abspath(args.isa_dir), ceres_root)

    if args.bench_dir:
        process_test_group("riscv-benchmarks", os.path.abspath(args.bench_dir), ceres_root)


if __name__ == "__main__":
    main()
