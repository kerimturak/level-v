#!/usr/bin/env python3
"""
compare_logs.py — Ceres vs Spike Commit Log Comparator (Enhanced)
===================================================================

Features:
  ✅ Run test makefileı farkları göstermek için bunu kullanır
  ✅ Ignores init cycles (PC < 0x80000000 or INST=0x0)
  ✅ Optional CSR-skip mode (--skip-csr)
  ✅ Optional resynchronization (--resync --window N)
  ✅ Compares PC/INST and register writes
  ✅ Colored console summary + visual side-by-side diff
  ✅ Beautiful HTML report with disassembly integration
  ✅ Shows PASS/FAIL addresses and test info
  ✅ Always outputs comparison statistics
"""
import sys
import re
import argparse
from colorama import Fore, Style, init
from html_diff_generator import generate_html_diff

init(autoreset=True)

# ============================================================
# Disassembly Parser
# ============================================================
def parse_disassembly(dump_file):
    """
    Parse .dump file and create address-to-instruction mapping.
    
    Args:
        dump_file: Path to disassembly dump file
    
    Returns:
        Dictionary mapping {address: (instruction, disassembly)}
        Example: {0x80000000: ("0540006f", "j 80000054 <reset_vector>")}
    """
    if not dump_file:
        return {}
    
    disasm_map = {}
    try:
        with open(dump_file, 'r', errors='ignore') as f:
            for line in f:
                # Match lines like: "80000000:	0540006f          	j	80000054 <reset_vector>"
                match = re.match(r'\s*([0-9a-f]+):\s+([0-9a-f]+)\s+(.+)', line, re.IGNORECASE)
                if match:
                    addr = int(match.group(1), 16)
                    inst_hex = match.group(2)
                    disasm = match.group(3).strip()
                    disasm_map[addr] = (inst_hex, disasm)
    except FileNotFoundError:
        print(f"{Fore.YELLOW}[WARNING]{Style.RESET_ALL} Dump file not found: {dump_file}")
    except Exception as e:
        print(f"{Fore.YELLOW}[WARNING]{Style.RESET_ALL} Error parsing dump file: {e}")
    
    return disasm_map


def parse_pass_fail_addresses(addr_file):
    """
    Parse pass/fail address file.
    
    Args:
        addr_file: Path to address file containing "PASS_ADDR FAIL_ADDR"
    
    Returns:
        Tuple (pass_addr, fail_addr) or (None, None) if file not found
    """
    if not addr_file:
        return None, None
    
    try:
        with open(addr_file, 'r') as f:
            line = f.readline().strip()
            parts = line.split()
            if len(parts) >= 2:
                pass_addr = int(parts[0], 16)
                fail_addr = int(parts[1], 16)
                return pass_addr, fail_addr
    except FileNotFoundError:
        print(f"{Fore.YELLOW}[WARNING]{Style.RESET_ALL} Address file not found: {addr_file}")
    except Exception as e:
        print(f"{Fore.YELLOW}[WARNING]{Style.RESET_ALL} Error parsing address file: {e}")
    
    return None, None


# ============================================================
# Log Parsing
# ============================================================
def normalize_line(line: str):
    """Parse and normalize a single commit log line."""
    line = line.strip()
    if not line or "core" not in line:
        return None
    line = re.sub(r"core\s*\d+:", "", line)
    line = re.sub(r"\s{2,}", " ", line)
    m = re.search(r"0x([0-9a-f]+)\s+\(0x([0-9a-f]+)\)(.*)", line)
    if not m:
        return None
    pc   = int(m.group(1), 16)
    inst = int(m.group(2), 16)
    rest = m.group(3).strip()
    return (pc, inst, rest, line)


CSR_KEYWORDS = [
    "csr", "mstatus", "sstatus", "ustatus",
    "mtvec", "stvec", "utvec",
    "medeleg", "mideleg", "mie", "mip",
    "satp", "mepc", "sepc", "uepc",
    "pmpcfg", "pmpaddr", "tvec", "tval"
]


def parse_log(path: str, skip_init=True, skip_csr=False):
    """
    Parse commit log file and return list of (pc, inst, rest, line) tuples.
    
    Args:
        path: Path to log file
        skip_init: Skip initialization cycles (PC < 0x80000000 or INST=0x0)
        skip_csr: Skip CSR-related instructions
    
    Returns:
        List of tuples: (pc, inst, rest, raw_line)
    """
    out = []
    with open(path, "r", errors="ignore") as f:
        for raw in f:
            if "core" not in raw:
                continue
            if skip_csr and any(kw in raw for kw in CSR_KEYWORDS):
                continue
            tup = normalize_line(raw)
            if not tup:
                continue
            pc, inst, rest, line = tup
            if skip_init and (pc < 0x80000000 or inst == 0x00000000):
                continue
            out.append((pc, inst, rest, line))
    return out


# ============================================================
# Comparison Logic
# ============================================================
def entries_equal(a, b):
    """Check if two entries have matching PC and INST."""
    return a[0] == b[0] and a[1] == b[1]


def try_resync(rtl, spike, i, j, window):
    """
    Attempt to resynchronize mismatched logs.
    
    Args:
        rtl: RTL log entries
        spike: Spike log entries
        i: Current RTL index
        j: Current Spike index
        window: Lookahead window size
    
    Returns:
        (new_i, new_j, reason) or (None, None, None) if no resync found
    """
    # Try skipping ahead in Spike
    if i < len(rtl) and j < len(spike):
        for dj in range(1, window+1):
            if j+dj < len(spike) and entries_equal(rtl[i], spike[j+dj]):
                return i, j+dj, f"resync: skipped {dj} in SPIKE"
    
    # Try skipping ahead in RTL
    if i < len(rtl) and j < len(spike):
        for di in range(1, window+1):
            if i+di < len(rtl) and entries_equal(rtl[i+di], spike[j]):
                return i+di, j, f"resync: skipped {di} in RTL"
    
    return None, None, None


# ============================================================
# Output Generators
# ============================================================
def print_comparison_header(rtl_count, spike_count):
    """Print comparison header with entry counts."""
    print(f"\n{Fore.CYAN}{'═' * 80}{Style.RESET_ALL}")
    print(f"{Fore.CYAN}{'CERES vs SPIKE — Commit Log Comparison':^80}{Style.RESET_ALL}")
    print(f"{Fore.CYAN}{'═' * 80}{Style.RESET_ALL}")
    print(f"{Fore.YELLOW}RTL entries    : {rtl_count:,}{Style.RESET_ALL}")
    print(f"{Fore.YELLOW}Spike entries  : {spike_count:,}{Style.RESET_ALL}")
    print(f"{Fore.CYAN}{'─' * 80}{Style.RESET_ALL}\n")


def print_summary(stats, has_errors):
    """
    Print detailed comparison summary.
    
    Args:
        stats: Dictionary of comparison statistics
        has_errors: Boolean indicating if errors were found
    """
    print(f"\n{Fore.CYAN}{'═' * 80}{Style.RESET_ALL}")
    print(f"{Fore.CYAN}{'COMPARISON SUMMARY':^80}{Style.RESET_ALL}")
    print(f"{Fore.CYAN}{'═' * 80}{Style.RESET_ALL}")
    
    total_compared = stats['match'] + stats['pcinst_mismatch'] + stats['reg_mismatch']
    match_rate = (stats['match'] / total_compared * 100) if total_compared > 0 else 0
    
    # Overall status
    if has_errors:
        status_icon = "❌"
        status_text = "FAILED - Differences Found"
        status_color = Fore.RED
    else:
        status_icon = "✅"
        status_text = "PASSED - Logs Match"
        status_color = Fore.GREEN
    
    print(f"\n{status_color}{'  ' + status_icon + ' ' + status_text:^80}{Style.RESET_ALL}\n")
    
    # Detailed statistics
    print(f"{Fore.YELLOW}Match Statistics:{Style.RESET_ALL}")
    print(f"  {Fore.GREEN}✅ Perfect matches      : {stats['match']:>8,} ({match_rate:.2f}%){Style.RESET_ALL}")
    print(f"  {Fore.RED}❌ PC/INST mismatches   : {stats['pcinst_mismatch']:>8,}{Style.RESET_ALL}")
    print(f"  {Fore.YELLOW}⚠️  Register mismatches : {stats['reg_mismatch']:>8,}{Style.RESET_ALL}")
    
    print(f"\n{Fore.YELLOW}Extra Entries:{Style.RESET_ALL}")
    print(f"  {Fore.CYAN}RTL extra entries       : {stats['insert_rtl']:>8,}{Style.RESET_ALL}")
    print(f"  {Fore.CYAN}Spike extra entries     : {stats['insert_spike']:>8,}{Style.RESET_ALL}")
    
    if stats.get('resyncs', 0) > 0:
        print(f"\n{Fore.YELLOW}Resynchronization:{Style.RESET_ALL}")
        print(f"  {Fore.MAGENTA}🔄 Resync events        : {stats['resyncs']:>8,}{Style.RESET_ALL}")
    
    print(f"\n{Fore.CYAN}{'─' * 80}{Style.RESET_ALL}")
    print(f"{Fore.YELLOW}Total cycles compared   : {total_compared:>8,}{Style.RESET_ALL}")
    print(f"{Fore.CYAN}{'═' * 80}{Style.RESET_ALL}\n")


def generate_visual_diff(rtl, spike, path, diffs):
    """
    Generate side-by-side visual diff file.
    
    Args:
        rtl: RTL log entries
        spike: Spike log entries
        path: Output file path
        diffs: List of (type, rtl_entry, spike_entry) tuples
    """
    with open(path, "w") as out:
        out.write("╔════════════════════════════════════════════════════════════════════════════════════════╗\n")
        out.write("║                               CERES vs SPIKE VISUAL DIFF                              ║\n")
        out.write("╚════════════════════════════════════════════════════════════════════════════════════════╝\n\n")

        maxlen = max(len(rtl), len(spike))
        for i in range(maxlen):
            rtl_str = f"PC=0x{rtl[i][0]:08x} INST=0x{rtl[i][1]:08x} {rtl[i][2]}" if i < len(rtl) else ""
            spk_str = f"PC=0x{spike[i][0]:08x} INST=0x{spike[i][1]:08x} {spike[i][2]}" if i < len(spike) else ""

            if i < len(rtl) and i < len(spike):
                if entries_equal(rtl[i], spike[i]):
                    if rtl[i][2].replace(" ","") == spike[i][2].replace(" ",""):
                        mark = "✅ MATCH "
                        color = Fore.GREEN
                    else:
                        mark = "⚠️ REG_MISMATCH "
                        color = Fore.YELLOW
                else:
                    mark = "❌ PC/INST MISMATCH"
                    color = Fore.RED
            elif i < len(rtl):
                mark = "➕ EXTRA RTL"
                color = Fore.CYAN
            else:
                mark = "➕ EXTRA SPIKE"
                color = Fore.MAGENTA

            #print(color + f"{mark:<18} | {rtl_str:<80} | {spk_str}" + Style.RESET_ALL)
            out.write(f"{mark:<18} | {rtl_str:<80} | {spk_str}\n")

    print(f"{Fore.CYAN}📄 Visual diff written to {path}{Style.RESET_ALL}")


def write_diff_status(output_file, stats, has_errors):
    """
    Write comparison status to output file.
    
    Args:
        output_file: Path to output file
        stats: Statistics dictionary
        has_errors: Whether errors were found
    """
    with open(output_file, "w") as f:
        f.write("=== CERES vs SPIKE Comparison Result ===\n\n")
        
        if has_errors:
            f.write("DIFF_STATUS=MISMATCH\n")
        else:
            f.write("DIFF_STATUS=MATCH\n")
        
        f.write("\n=== Statistics ===\n")
        f.write(f"Perfect Matches     : {stats['match']}\n")
        f.write(f"PC/INST Mismatches  : {stats['pcinst_mismatch']}\n")
        f.write(f"Register Mismatches : {stats['reg_mismatch']}\n")
        f.write(f"RTL Extra Entries   : {stats['insert_rtl']}\n")
        f.write(f"Spike Extra Entries : {stats['insert_spike']}\n")
        f.write(f"Resync Events       : {stats.get('resyncs', 0)}\n")


# ============================================================
# Main Comparison Function
# ============================================================
def compare_logs(rtl, spike, output_file, enable_resync=False, window=0, 
                disasm_map=None, pass_addr=None, fail_addr=None, test_name=None):
    """
    Compare RTL and Spike logs and generate reports.
    
    Args:
        rtl: List of RTL log entries
        spike: List of Spike log entries
        output_file: Base path for output files
        enable_resync: Enable resynchronization
        window: Resync window size
        disasm_map: Dictionary of PC->disassembly mappings
        pass_addr: Test pass address
        fail_addr: Test fail address
        test_name: Name of the test
    """
    diffs = []
    stats = {
        "match": 0,
        "insert_spike": 0,
        "insert_rtl": 0,
        "reg_mismatch": 0,
        "pcinst_mismatch": 0,
        "resyncs": 0
    }

    i = j = 0
    while i < len(rtl) and j < len(spike):
        r = rtl[i]
        s = spike[j]

        if entries_equal(r, s):
            if r[2].replace(" ","") != s[2].replace(" ",""):
                diffs.append(("REG", r, s))
                stats["reg_mismatch"] += 1
            else:
                stats["match"] += 1
            i += 1
            j += 1
            continue

        if enable_resync:
            ni, nj, why = try_resync(rtl, spike, i, j, window)
            if ni is not None:
                if nj > j:
                    for jj in range(j, nj):
                        diffs.append(("INS_SPIKE", None, spike[jj]))
                        stats["insert_spike"] += 1
                if ni > i:
                    for ii in range(i, ni):
                        diffs.append(("INS_RTL", rtl[ii], None))
                        stats["insert_rtl"] += 1
                i, j = ni, nj
                stats["resyncs"] += 1
                continue

        diffs.append(("PCINST", r, s))
        stats["pcinst_mismatch"] += 1
        i += 1
        j += 1

    # Handle remaining entries
    while i < len(rtl):
        diffs.append(("TAIL_RTL", rtl[i], None))
        stats["insert_rtl"] += 1
        i += 1
    
    while j < len(spike):
        diffs.append(("TAIL_SPIKE", None, spike[j]))
        stats["insert_spike"] += 1
        j += 1

    # Determine if there are errors
    has_errors = (stats['pcinst_mismatch'] > 0 or 
                  stats['reg_mismatch'] > 0 or 
                  stats['insert_rtl'] > 0 or 
                  stats['insert_spike'] > 0)

    # Generate all output files
    print(f"\n{Fore.CYAN}{'─' * 80}{Style.RESET_ALL}")
    print(f"{Fore.CYAN}Generating output files...{Style.RESET_ALL}")
    print(f"{Fore.CYAN}{'─' * 80}{Style.RESET_ALL}\n")
    
    # 1. Write status file
    write_diff_status(output_file, stats, has_errors)
    print(f"{Fore.GREEN}✓{Style.RESET_ALL} Status file    : {output_file}")
    
    # 2. Generate visual diff
    visual_diff_path = output_file.replace(".log", "_visual_diff.log")
    generate_visual_diff(rtl, spike, visual_diff_path, diffs)
    
    # 3. Generate HTML report with enhanced info
    html_path = output_file.replace(".log", ".html")
    generate_html_diff(rtl, spike, html_path, stats, disasm_map, 
                      pass_addr, fail_addr, test_name)
    
    # 4. Print summary to console
    print_summary(stats, has_errors)
    
    # Exit with appropriate status
    if has_errors:
        sys.exit(1)
    else:
        print(f"{Fore.GREEN}✅ Comparison PASSED - Logs match perfectly!{Style.RESET_ALL}\n")
        sys.exit(0)


# ============================================================
# CLI Entry Point
# ============================================================
def main():
    """Main entry point for command-line usage."""
    ap = argparse.ArgumentParser(
        description="Compare CERES RTL vs Spike commit logs",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --rtl rtl.log --spike spike.log --output diff.log
  %(prog)s --rtl rtl.log --spike spike.log --output diff.log --skip-csr
  %(prog)s --rtl rtl.log --spike spike.log --output diff.log --dump test.dump --addr addr.txt
  %(prog)s --rtl rtl.log --spike spike.log --output diff.log --resync --window 16
        """
    )
    
    ap.add_argument("--rtl", required=True, help="Path to RTL commit log")
    ap.add_argument("--spike", required=True, help="Path to Spike commit log")
    ap.add_argument("--output", required=True, help="Output file path")
    ap.add_argument("--dump", help="Path to disassembly dump file (.dump)")
    ap.add_argument("--addr", help="Path to pass/fail address file")
    ap.add_argument("--test-name", help="Test name (auto-detected from paths if not provided)")
    ap.add_argument("--skip-csr", action="store_true", 
                    help="Ignore CSR-related instructions")
    ap.add_argument("--resync", action="store_true", 
                    help="Enable resynchronization on mismatches")
    ap.add_argument("--window", type=int, default=8, 
                    help="Resync lookahead window size (default: 8)")
    
    args = ap.parse_args()

    # Auto-detect test name from file paths if not provided
    test_name = args.test_name
    if not test_name:
        # Try to extract from output path: .../rv32ui-p-add/diff.log -> rv32ui-p-add
        import os
        test_name = os.path.basename(os.path.dirname(args.output))

    # Parse optional files
    disasm_map = parse_disassembly(args.dump) if args.dump else {}
    pass_addr, fail_addr = parse_pass_fail_addresses(args.addr) if args.addr else (None, None)

    # Print header
    print(f"\n{Fore.CYAN}{'═' * 80}{Style.RESET_ALL}")
    print(f"{Fore.CYAN}{'CERES RISC-V — Log Comparison Tool':^80}{Style.RESET_ALL}")
    print(f"{Fore.CYAN}{'═' * 80}{Style.RESET_ALL}")
    print(f"\n{Fore.YELLOW}Configuration:{Style.RESET_ALL}")
    print(f"  Test name    : {test_name or 'N/A'}")
    print(f"  RTL log      : {args.rtl}")
    print(f"  Spike log    : {args.spike}")
    print(f"  Output       : {args.output}")
    if args.dump:
        print(f"  Disassembly  : {args.dump} ({len(disasm_map)} instructions)")
    if args.addr:
        if pass_addr is not None:
            print(f"  Pass address : 0x{pass_addr:08x}")
            print(f"  Fail address : 0x{fail_addr:08x}")
        else:
            print(f"  Address file : {args.addr} (failed to parse)")
    print(f"  Skip CSR     : {args.skip_csr}")
    print(f"  Resync       : {args.resync}")
    if args.resync:
        print(f"  Resync window: {args.window}")

    # Parse logs
    print(f"\n{Fore.CYAN}Parsing log files...{Style.RESET_ALL}")
    rtl   = parse_log(args.rtl, skip_init=True, skip_csr=args.skip_csr)
    spike = parse_log(args.spike, skip_init=True, skip_csr=args.skip_csr)
    
    print_comparison_header(len(rtl), len(spike))

    # Compare
    compare_logs(rtl, spike, args.output, 
                enable_resync=args.resync, window=args.window,
                disasm_map=disasm_map, pass_addr=pass_addr, 
                fail_addr=fail_addr, test_name=test_name)


if __name__ == "__main__":
    main()

