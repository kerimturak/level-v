#!/usr/bin/env python3
"""
List static memory usage for every *.elf under build/tests (and optional .mem line count).

Usage:
  python3 script/python/levelv_elf_memory_report.py [build/tests_root] [riscv-prefix]

Example:
  make levelv_memory_report
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path


def main() -> int:
    repo = Path(__file__).resolve().parents[2]
    tests_root = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else repo / "build" / "tests"
    prefix = sys.argv[2] if len(sys.argv) > 2 else "riscv32-unknown-elf"
    size_bin = f"{prefix}-size"

    elves = sorted(tests_root.rglob("*.elf"))
    if not elves:
        print(f"No ELF files under {tests_root}", file=sys.stderr)
        return 0

    print(
        f"{'suite':<20} {'elf':<40} {'text':>7} {'data':>7} {'bss':>7} {'dec':>8} "
        f"{'mem_lines':>10}  notes"
    )
    by_suite: dict[str, list[int]] = {}

    for elf in elves:
        rel = elf.relative_to(tests_root)
        suite = rel.parts[0] if rel.parts else "."
        name = rel.name

        try:
            out = subprocess.check_output([size_bin, str(elf)], text=True, timeout=30)
        except (subprocess.CalledProcessError, FileNotFoundError, OSError) as e:
            print(f"{suite:<20} {name:<40} {'ERROR':>7} {e}", flush=True)
            continue

        lines = [ln.strip() for ln in out.strip().splitlines() if ln.strip()]
        if not lines:
            continue
        toks = lines[-1].split()
        if len(toks) < 4:
            continue
        try:
            text, data, bss, dec = int(toks[0]), int(toks[1]), int(toks[2]), int(toks[3])
        except ValueError:
            continue

        mem_lines = ""
        mem_path = None
        if "embench" in rel.parts and (elf.parent.name == "elf"):
            mem_path = tests_root / "embench" / "mem" / (elf.stem + ".mem")
        elif elf.parent.resolve() == (tests_root / "dhrystone").resolve():
            mem_path = tests_root / "dhrystone" / (elf.stem + ".mem")
        elif elf.parent.resolve() == (tests_root / "coremark").resolve():
            mem_path = tests_root / "coremark" / (elf.stem + ".mem")
        elif "riscv-tests" in rel.parts:
            mem_path = tests_root / "riscv-tests" / "mem" / (elf.stem + ".mem")
        if mem_path and mem_path.is_file():
            with open(mem_path, encoding="utf-8", errors="replace") as f:
                mem_lines = str(sum(1 for _ in f))

        note = ""
        if dec > 32768:
            note = ">32KiB"
        by_suite.setdefault(suite, []).append(dec)

        print(
            f"{suite:<20} {name:<40} {text:>7} {data:>7} {bss:>7} {dec:>8} {mem_lines:>10}  {note}"
        )

    print()
    print("Per-suite max(dec) — use for BRAM / link.ld LENGTH budgeting:")
    for suite in sorted(by_suite.keys()):
        mx = max(by_suite[suite])
        print(f"  {suite:<22} max(dec)={mx:6d}  ({mx / 1024:.2f} KiB)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
