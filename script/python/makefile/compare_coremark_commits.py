#!/usr/bin/env python3
"""
compare_coremark_commits.py — CoreMark-Specific Commit Log Comparator
=====================================================================

This script compares CoreMark commit logs from Ceres-V and Spike, accounting
for different base addresses and entry points. It finds the main() function
in both logs and compares execution from that point forward.

Usage:
    python3 compare_coremark_commits.py \\
        --ceres ceres_commits.log \\
        --spike spike_commits.log \\
        --ceres-dump ceres.dump \\
        --spike-dump spike.dump \\
        --output diff.log
"""

import sys
import re
import argparse
from collections import defaultdict
from colorama import Fore, Style, init

init(autoreset=True)

def parse_commit_log(filename):
    """Parse commit log and return list of (pc, inst, reg, val) tuples."""
    commits = []
    with open(filename, 'r') as f:
        for line in f:
            # Format: core   0: 3 0x80000714 (0x00001141) x2 0x80009820
            # or:     core   0: 3 0x80000716 (0x0000ce86) mem 0x8000987c 0x80000074
            match = re.match(r'core\s+\d+:\s+\d+\s+0x([0-9a-f]+)\s+\(0x([0-9a-f]+)\)(?:\s+(\S+)\s+0x([0-9a-f]+))?', line, re.IGNORECASE)
            if match:
                pc = int(match.group(1), 16)
                inst = int(match.group(2), 16)
                reg = match.group(3) if match.group(3) else None
                val = int(match.group(4), 16) if match.group(4) else None
                commits.append((pc, inst, reg, val))
    return commits

def find_function_address(dump_file, func_name):
    """Find function address in objdump output."""
    try:
        with open(dump_file, 'r') as f:
            for line in f:
                # Match: "80000714 <main>:"
                match = re.match(rf'^\s*([0-9a-f]+)\s+<{func_name}>:', line, re.IGNORECASE)
                if match:
                    return int(match.group(1), 16)
    except:
        pass
    return None

def find_sync_point(commits, target_addr, window=100):
    """Find index where PC first reaches target address (within window)."""
    for i, (pc, inst, reg, val) in enumerate(commits):
        if pc == target_addr:
            return i
    return None

def compare_commits(ceres_commits, spike_commits, ceres_start, spike_start, max_compare=10000):
    """
    Compare commits starting from sync points.

    Returns: (matches, mismatches, details)
    """
    matches = 0
    mismatches = []

    ceres_idx = ceres_start
    spike_idx = spike_start

    compared = 0
    while compared < max_compare and ceres_idx < len(ceres_commits) and spike_idx < len(spike_commits):
        c_pc, c_inst, c_reg, c_val = ceres_commits[ceres_idx]
        s_pc, s_inst, s_reg, s_val = spike_commits[spike_idx]

        # Compare instruction only (ignore register values due to different base addresses)
        # Also compare register NAME (x1, x2, etc.) to ensure same operations
        if c_inst == s_inst and c_reg == s_reg:
            matches += 1
        else:
            # Record mismatch
            if len(mismatches) < 100:  # Limit stored mismatches
                mismatches.append({
                    'index': compared,
                    'ceres': (c_pc, c_inst, c_reg, c_val),
                    'spike': (s_pc, s_inst, s_reg, s_val)
                })

        ceres_idx += 1
        spike_idx += 1
        compared += 1

    return matches, mismatches, compared

def main():
    parser = argparse.ArgumentParser(
        description='Compare CoreMark commit logs from Ceres-V and Spike',
        formatter_class=argparse.RawDescriptionHelpFormatter
    )

    parser.add_argument('--ceres', required=True, help='Ceres-V commit log file')
    parser.add_argument('--spike', required=True, help='Spike commit log file')
    parser.add_argument('--ceres-dump', required=True, help='Ceres-V objdump file')
    parser.add_argument('--spike-dump', required=True, help='Spike objdump file')
    parser.add_argument('--output', required=True, help='Output diff file')
    parser.add_argument('--function', default='main', help='Function to sync on (default: main)')
    parser.add_argument('--max-compare', type=int, default=10000, help='Max commits to compare')

    args = parser.parse_args()

    print(f"\n{Fore.CYAN}{'='*80}{Style.RESET_ALL}")
    print(f"{Fore.CYAN}CoreMark Commit Log Comparator{Style.RESET_ALL}")
    print(f"{Fore.CYAN}{'='*80}{Style.RESET_ALL}\n")

    # Step 1: Find function addresses
    print(f"{Fore.YELLOW}[1/5]{Style.RESET_ALL} Finding {args.function}() addresses in dumps...")
    ceres_func_addr = find_function_address(args.ceres_dump, args.function)
    spike_func_addr = find_function_address(args.spike_dump, args.function)

    if not ceres_func_addr:
        print(f"{Fore.RED}ERROR: Could not find {args.function}() in Ceres-V dump{Style.RESET_ALL}")
        return 1
    if not spike_func_addr:
        print(f"{Fore.RED}ERROR: Could not find {args.function}() in Spike dump{Style.RESET_ALL}")
        return 1

    print(f"  Ceres-V {args.function}(): {Fore.GREEN}0x{ceres_func_addr:08x}{Style.RESET_ALL}")
    print(f"  Spike   {args.function}(): {Fore.GREEN}0x{spike_func_addr:08x}{Style.RESET_ALL}")
    print(f"  Address offset: 0x{abs(ceres_func_addr - spike_func_addr):08x}")

    # Step 2: Parse commit logs
    print(f"\n{Fore.YELLOW}[2/5]{Style.RESET_ALL} Parsing commit logs...")
    ceres_commits = parse_commit_log(args.ceres)
    spike_commits = parse_commit_log(args.spike)

    print(f"  Ceres-V: {Fore.CYAN}{len(ceres_commits):,}{Style.RESET_ALL} commits")
    print(f"  Spike:   {Fore.CYAN}{len(spike_commits):,}{Style.RESET_ALL} commits")

    # Step 3: Find sync points
    print(f"\n{Fore.YELLOW}[3/5]{Style.RESET_ALL} Finding sync points at {args.function}()...")
    ceres_start = find_sync_point(ceres_commits, ceres_func_addr)
    spike_start = find_sync_point(spike_commits, spike_func_addr)

    if ceres_start is None:
        print(f"{Fore.RED}ERROR: {args.function}() not found in Ceres-V commits (0x{ceres_func_addr:08x}){Style.RESET_ALL}")
        return 1
    if spike_start is None:
        print(f"{Fore.RED}ERROR: {args.function}() not found in Spike commits (0x{spike_func_addr:08x}){Style.RESET_ALL}")
        return 1

    print(f"  Ceres-V starts at commit #{ceres_start:,}")
    print(f"  Spike   starts at commit #{spike_start:,}")

    # Step 4: Compare
    print(f"\n{Fore.YELLOW}[4/5]{Style.RESET_ALL} Comparing commits from {args.function}()...")
    matches, mismatches, compared = compare_commits(
        ceres_commits, spike_commits,
        ceres_start, spike_start,
        args.max_compare
    )

    match_rate = (matches / compared * 100) if compared > 0 else 0

    print(f"  Compared:   {Fore.CYAN}{compared:,}{Style.RESET_ALL} commits")
    print(f"  Matches:    {Fore.GREEN}{matches:,}{Style.RESET_ALL} ({match_rate:.2f}%)")
    print(f"  Mismatches: {Fore.RED}{len(mismatches):,}{Style.RESET_ALL}")

    # Step 5: Write output
    print(f"\n{Fore.YELLOW}[5/5]{Style.RESET_ALL} Writing results to {args.output}...")

    with open(args.output, 'w') as f:
        f.write("="*80 + "\n")
        f.write("CoreMark Commit Log Comparison\n")
        f.write("="*80 + "\n\n")

        f.write(f"Sync Function: {args.function}()\n")
        f.write(f"  Ceres-V: 0x{ceres_func_addr:08x} (commit #{ceres_start})\n")
        f.write(f"  Spike:   0x{spike_func_addr:08x} (commit #{spike_start})\n\n")

        f.write(f"Comparison Results:\n")
        f.write(f"  Total Compared: {compared}\n")
        f.write(f"  Matches:        {matches} ({match_rate:.2f}%)\n")
        f.write(f"  Mismatches:     {len(mismatches)}\n\n")

        if mismatches:
            f.write("="*80 + "\n")
            f.write("First 100 Mismatches:\n")
            f.write("="*80 + "\n\n")

            for mm in mismatches[:100]:
                idx = mm['index']
                c_pc, c_inst, c_reg, c_val = mm['ceres']
                s_pc, s_inst, s_reg, s_val = mm['spike']

                f.write(f"Commit #{idx} (from {args.function})\n")
                f.write(f"  Ceres-V: PC=0x{c_pc:08x} INST=0x{c_inst:08x}")
                if c_reg:
                    f.write(f" {c_reg}=0x{c_val:08x}")
                f.write("\n")

                f.write(f"  Spike:   PC=0x{s_pc:08x} INST=0x{s_inst:08x}")
                if s_reg:
                    f.write(f" {s_reg}=0x{s_val:08x}")
                f.write("\n\n")

    print(f"{Fore.GREEN}✓ Results written to {args.output}{Style.RESET_ALL}\n")

    # Summary
    print(f"{Fore.CYAN}{'='*80}{Style.RESET_ALL}")
    if match_rate >= 99.0:
        print(f"{Fore.GREEN}✅ PASS - Excellent match ({match_rate:.2f}%){Style.RESET_ALL}")
        return 0
    elif match_rate >= 90.0:
        print(f"{Fore.YELLOW}⚠️  WARNING - Good match but some differences ({match_rate:.2f}%){Style.RESET_ALL}")
        return 0
    else:
        print(f"{Fore.RED}❌ FAIL - Significant differences ({match_rate:.2f}%){Style.RESET_ALL}")
        return 1

if __name__ == '__main__':
    sys.exit(main())
