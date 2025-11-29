#!/usr/bin/env python3
"""
compare_logs.py — Ceres vs Spike Commit Log Comparator (Enhanced v2.0)
======================================================================

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
  ✅ JSON output support (--json)
  ✅ Verbose mode with progress indicator (--verbose)
  ✅ Quiet mode for CI/CD pipelines (--quiet)
  ✅ Maximum error limit (--max-errors)
  ✅ Context lines around errors (--context)
  ✅ Summary-only mode (--summary-only)
  ✅ Exit code control (--no-fail)
"""
import sys
import re
import os
import argparse
import json
import time
from datetime import datetime
from colorama import Fore, Style, init
from html_diff_generator import generate_html_diff

init(autoreset=True)

# Global verbosity level
VERBOSE = False
QUIET = False

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


def parse_log(path: str, skip_init=True, skip_csr=False, show_progress=False):
    """
    Parse commit log file and return list of (pc, inst, rest, line) tuples.
    
    Args:
        path: Path to log file
        skip_init: Skip initialization cycles (PC < 0x80000000 or INST=0x0)
        skip_csr: Skip CSR-related instructions
        show_progress: Show progress indicator while parsing
    
    Returns:
        List of tuples: (pc, inst, rest, raw_line)
    """
    out = []
    line_count = 0
    
    # Get file size for progress
    file_size = os.path.getsize(path) if show_progress else 0
    bytes_read = 0
    last_progress = 0
    
    with open(path, "r", errors="ignore") as f:
        for raw in f:
            line_count += 1
            bytes_read += len(raw)
            
            # Show progress every 10%
            if show_progress and file_size > 0:
                progress = int((bytes_read / file_size) * 100)
                if progress >= last_progress + 10:
                    print(f"\r  Parsing {os.path.basename(path)}: {progress}%", end="", flush=True)
                    last_progress = progress
            
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
    
    if show_progress:
        print(f"\r  Parsing {os.path.basename(path)}: 100% ({len(out):,} entries from {line_count:,} lines)")
    
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


def print_summary(stats, has_errors, elapsed_time=None, test_name=None):
    """
    Print detailed comparison summary.
    
    Args:
        stats: Dictionary of comparison statistics
        has_errors: Boolean indicating if errors were found
        elapsed_time: Time taken for comparison (optional)
        test_name: Name of the test (optional)
    """
    if QUIET:
        # Minimal output for CI/CD
        status = "FAIL" if has_errors else "PASS"
        print(f"[{status}] {test_name or 'test'}: match={stats['match']}, mismatch={stats['pcinst_mismatch']+stats['reg_mismatch']}")
        return
    
    print(f"\n{Fore.CYAN}{'═' * 80}{Style.RESET_ALL}")
    print(f"{Fore.CYAN}{'COMPARISON SUMMARY':^80}{Style.RESET_ALL}")
    if test_name:
        print(f"{Fore.CYAN}{test_name:^80}{Style.RESET_ALL}")
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
    
    # Detailed statistics table
    print(f"{Fore.YELLOW}┌{'─' * 40}┬{'─' * 20}┐{Style.RESET_ALL}")
    print(f"{Fore.YELLOW}│{'Match Statistics':^40}│{'Count':^20}│{Style.RESET_ALL}")
    print(f"{Fore.YELLOW}├{'─' * 40}┼{'─' * 20}┤{Style.RESET_ALL}")
    print(f"{Fore.GREEN}│ ✅ Perfect matches                     │{stats['match']:>18,} │{Style.RESET_ALL}")
    print(f"{Fore.RED}│ ❌ PC/INST mismatches                  │{stats['pcinst_mismatch']:>18,} │{Style.RESET_ALL}")
    print(f"{Fore.YELLOW}│ ⚠️  Register mismatches                │{stats['reg_mismatch']:>18,} │{Style.RESET_ALL}")
    print(f"{Fore.CYAN}│ ➕ RTL extra entries                   │{stats['insert_rtl']:>18,} │{Style.RESET_ALL}")
    print(f"{Fore.CYAN}│ ➕ Spike extra entries                 │{stats['insert_spike']:>18,} │{Style.RESET_ALL}")
    if stats.get('resyncs', 0) > 0:
        print(f"{Fore.MAGENTA}│ 🔄 Resync events                       │{stats['resyncs']:>18,} │{Style.RESET_ALL}")
    print(f"{Fore.YELLOW}├{'─' * 40}┼{'─' * 20}┤{Style.RESET_ALL}")
    print(f"{Fore.WHITE}│ {'Total cycles compared':40}│{total_compared:>18,} │{Style.RESET_ALL}")
    print(f"{Fore.WHITE}│ {'Match rate':40}│{match_rate:>17.2f}% │{Style.RESET_ALL}")
    if elapsed_time:
        print(f"{Fore.WHITE}│ {'Elapsed time':40}│{elapsed_time:>16.2f}s │{Style.RESET_ALL}")
    print(f"{Fore.YELLOW}└{'─' * 40}┴{'─' * 20}┘{Style.RESET_ALL}\n")


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

            out.write(f"{mark:<18} | {rtl_str:<80} | {spk_str}\n")

    if not QUIET:
        print(f"{Fore.CYAN}📄 Visual diff written to {path}{Style.RESET_ALL}")


def write_diff_status(output_file, stats, has_errors, test_name=None, 
                      elapsed_time=None, write_json=False):
    """
    Write comparison status to output file.
    
    Args:
        output_file: Path to output file
        stats: Statistics dictionary
        has_errors: Whether errors were found
        test_name: Name of the test
        elapsed_time: Time taken for comparison
        write_json: Also write JSON format
    """
    timestamp = datetime.now().isoformat()
    total = stats['match'] + stats['pcinst_mismatch'] + stats['reg_mismatch']
    match_rate = (stats['match'] / total * 100) if total > 0 else 0
    
    with open(output_file, "w") as f:
        f.write("=== CERES vs SPIKE Comparison Result ===\n")
        f.write(f"Timestamp: {timestamp}\n")
        if test_name:
            f.write(f"Test Name: {test_name}\n")
        f.write("\n")
        
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
        f.write(f"Match Rate          : {match_rate:.2f}%\n")
        if elapsed_time:
            f.write(f"Elapsed Time        : {elapsed_time:.2f}s\n")
    
    # Write JSON if requested
    if write_json:
        json_file = output_file.replace('.log', '.json')
        json_data = {
            "timestamp": timestamp,
            "test_name": test_name,
            "status": "MISMATCH" if has_errors else "MATCH",
            "passed": not has_errors,
            "statistics": {
                "perfect_matches": stats['match'],
                "pcinst_mismatches": stats['pcinst_mismatch'],
                "register_mismatches": stats['reg_mismatch'],
                "rtl_extra": stats['insert_rtl'],
                "spike_extra": stats['insert_spike'],
                "resyncs": stats.get('resyncs', 0),
                "total_compared": total,
                "match_rate": round(match_rate, 2)
            },
            "elapsed_time": round(elapsed_time, 2) if elapsed_time else None
        }
        with open(json_file, "w") as f:
            json.dump(json_data, f, indent=2)
        
        if not QUIET:
            print(f"{Fore.GREEN}✓{Style.RESET_ALL} JSON report   : {json_file}")


# ============================================================
# Main Comparison Function
# ============================================================
def compare_logs(rtl, spike, output_file, enable_resync=False, window=0, 
                disasm_map=None, pass_addr=None, fail_addr=None, test_name=None,
                max_errors=None, no_fail=False, summary_only=False, write_json=False):
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
        max_errors: Stop after N errors (None = no limit)
        no_fail: Don't exit with error code on mismatch
        summary_only: Only generate summary, skip visual diff
        write_json: Write JSON output file
    """
    start_time = time.time()
    diffs = []
    stats = {
        "match": 0,
        "insert_spike": 0,
        "insert_rtl": 0,
        "reg_mismatch": 0,
        "pcinst_mismatch": 0,
        "resyncs": 0
    }
    
    error_count = 0
    max_errors_reached = False

    i = j = 0
    total_entries = max(len(rtl), len(spike))
    last_progress = 0
    
    while i < len(rtl) and j < len(spike):
        # Show progress for verbose mode
        if VERBOSE and total_entries > 0:
            progress = int(((i + j) / (2 * total_entries)) * 100)
            if progress >= last_progress + 5:
                print(f"\r  Comparing: {progress}%", end="", flush=True)
                last_progress = progress
        
        # Check max errors limit
        if max_errors is not None and error_count >= max_errors:
            max_errors_reached = True
            break
        
        r = rtl[i]
        s = spike[j]

        if entries_equal(r, s):
            if r[2].replace(" ","") != s[2].replace(" ",""):
                diffs.append(("REG", r, s))
                stats["reg_mismatch"] += 1
                error_count += 1
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
                        error_count += 1
                if ni > i:
                    for ii in range(i, ni):
                        diffs.append(("INS_RTL", rtl[ii], None))
                        stats["insert_rtl"] += 1
                        error_count += 1
                i, j = ni, nj
                stats["resyncs"] += 1
                continue

        diffs.append(("PCINST", r, s))
        stats["pcinst_mismatch"] += 1
        error_count += 1
        i += 1
        j += 1
    
    if VERBOSE:
        print("\r  Comparing: 100%    ")

    # Handle remaining entries (if not stopped by max_errors)
    if not max_errors_reached:
        while i < len(rtl):
            diffs.append(("TAIL_RTL", rtl[i], None))
            stats["insert_rtl"] += 1
            i += 1
        
        while j < len(spike):
            diffs.append(("TAIL_SPIKE", None, spike[j]))
            stats["insert_spike"] += 1
            j += 1

    elapsed_time = time.time() - start_time

    # Determine if there are errors
    has_errors = (stats['pcinst_mismatch'] > 0 or 
                  stats['reg_mismatch'] > 0 or 
                  stats['insert_rtl'] > 0 or 
                  stats['insert_spike'] > 0)

    if not QUIET:
        # Generate all output files
        print(f"\n{Fore.CYAN}{'─' * 80}{Style.RESET_ALL}")
        print(f"{Fore.CYAN}Generating output files...{Style.RESET_ALL}")
        print(f"{Fore.CYAN}{'─' * 80}{Style.RESET_ALL}\n")
    
    # 1. Write status file
    write_diff_status(output_file, stats, has_errors, test_name, 
                      elapsed_time, write_json)
    if not QUIET:
        print(f"{Fore.GREEN}✓{Style.RESET_ALL} Status file    : {output_file}")
    
    # 2. Generate visual diff (unless summary_only)
    if not summary_only:
        visual_diff_path = output_file.replace(".log", "_visual_diff.log")
        generate_visual_diff(rtl, spike, visual_diff_path, diffs)
    
    # 3. Generate HTML report with enhanced info
    html_path = output_file.replace(".log", ".html")
    generate_html_diff(rtl, spike, html_path, stats, disasm_map, 
                      pass_addr, fail_addr, test_name)
    
    # 4. Print summary to console
    print_summary(stats, has_errors, elapsed_time, test_name)
    
    # Print max errors warning
    if max_errors_reached and not QUIET:
        print(f"{Fore.YELLOW}⚠️  Stopped after {max_errors} errors (use --max-errors to change){Style.RESET_ALL}\n")
    
    # Exit with appropriate status
    if has_errors and not no_fail:
        sys.exit(1)
    else:
        if not QUIET:
            if has_errors:
                print(f"{Fore.YELLOW}⚠️  Comparison has errors but --no-fail was specified{Style.RESET_ALL}\n")
            else:
                print(f"{Fore.GREEN}✅ Comparison PASSED - Logs match perfectly!{Style.RESET_ALL}\n")
        sys.exit(0)


# ============================================================
# CLI Entry Point
# ============================================================
def main():
    """Main entry point for command-line usage."""
    global VERBOSE, QUIET
    
    ap = argparse.ArgumentParser(
        description="Compare CERES RTL vs Spike commit logs (v2.0)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Basic comparison
  %(prog)s --rtl rtl.log --spike spike.log --output diff.log
  
  # Skip CSR instructions
  %(prog)s --rtl rtl.log --spike spike.log --output diff.log --skip-csr
  
  # With disassembly and address info
  %(prog)s --rtl rtl.log --spike spike.log --output diff.log --dump test.dump --addr addr.txt
  
  # Enable resync with custom window
  %(prog)s --rtl rtl.log --spike spike.log --output diff.log --resync --window 16
  
  # CI/CD mode (quiet, JSON output, no fail)
  %(prog)s --rtl rtl.log --spike spike.log --output diff.log --quiet --json --no-fail
  
  # Verbose mode with max errors limit
  %(prog)s --rtl rtl.log --spike spike.log --output diff.log --verbose --max-errors 100

Exit Codes:
  0 - Logs match (or --no-fail specified)
  1 - Logs have differences
  2 - Error during execution
        """
    )
    
    # Required arguments
    req = ap.add_argument_group('Required arguments')
    req.add_argument("--rtl", required=True, help="Path to RTL commit log")
    req.add_argument("--spike", required=True, help="Path to Spike commit log")
    req.add_argument("--output", required=True, help="Output file path")
    
    # Optional input files
    inp = ap.add_argument_group('Input options')
    inp.add_argument("--dump", help="Path to disassembly dump file (.dump)")
    inp.add_argument("--addr", help="Path to pass/fail address file")
    inp.add_argument("--test-name", help="Test name (auto-detected from paths if not provided)")
    
    # Comparison options
    comp = ap.add_argument_group('Comparison options')
    comp.add_argument("--skip-csr", action="store_true", 
                      help="Ignore CSR-related instructions")
    comp.add_argument("--resync", action="store_true", 
                      help="Enable resynchronization on mismatches")
    comp.add_argument("--window", type=int, default=8, 
                      help="Resync lookahead window size (default: 8)")
    comp.add_argument("--max-errors", type=int, metavar="N",
                      help="Stop comparison after N errors")
    
    # Output options
    out = ap.add_argument_group('Output options')
    out.add_argument("--json", action="store_true",
                     help="Generate JSON output file")
    out.add_argument("--summary-only", action="store_true",
                     help="Only generate summary (skip visual diff)")
    out.add_argument("--no-fail", action="store_true",
                     help="Don't exit with error code on mismatch")
    
    # Verbosity
    verb = ap.add_argument_group('Verbosity options')
    verb.add_argument("-v", "--verbose", action="store_true",
                      help="Verbose output with progress indicators")
    verb.add_argument("-q", "--quiet", action="store_true",
                      help="Minimal output (for CI/CD pipelines)")
    
    args = ap.parse_args()
    
    # Set global verbosity
    VERBOSE = args.verbose
    QUIET = args.quiet
    
    if VERBOSE and QUIET:
        print(f"{Fore.YELLOW}Warning: Both --verbose and --quiet specified, using --quiet{Style.RESET_ALL}")
        VERBOSE = False

    # Auto-detect test name from file paths if not provided
    test_name = args.test_name
    if not test_name:
        test_name = os.path.basename(os.path.dirname(args.output))

    # Parse optional files
    disasm_map = parse_disassembly(args.dump) if args.dump else {}
    pass_addr, fail_addr = parse_pass_fail_addresses(args.addr) if args.addr else (None, None)

    if not QUIET:
        # Print header
        print(f"\n{Fore.CYAN}{'═' * 80}{Style.RESET_ALL}")
        print(f"{Fore.CYAN}{'CERES RISC-V — Log Comparison Tool v2.0':^80}{Style.RESET_ALL}")
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
        if args.max_errors:
            print(f"  Max errors   : {args.max_errors}")
        if args.json:
            print(f"  JSON output  : enabled")
        if args.no_fail:
            print(f"  No-fail mode : enabled")

    try:
        # Parse logs
        if not QUIET:
            print(f"\n{Fore.CYAN}Parsing log files...{Style.RESET_ALL}")
        
        rtl = parse_log(args.rtl, skip_init=True, skip_csr=args.skip_csr, 
                        show_progress=VERBOSE)
        spike = parse_log(args.spike, skip_init=True, skip_csr=args.skip_csr,
                          show_progress=VERBOSE)
        
        if not QUIET:
            print_comparison_header(len(rtl), len(spike))

        # Compare
        compare_logs(rtl, spike, args.output, 
                    enable_resync=args.resync, window=args.window,
                    disasm_map=disasm_map, pass_addr=pass_addr, 
                    fail_addr=fail_addr, test_name=test_name,
                    max_errors=args.max_errors, no_fail=args.no_fail,
                    summary_only=args.summary_only, write_json=args.json)
                    
    except FileNotFoundError as e:
        print(f"{Fore.RED}Error: File not found - {e}{Style.RESET_ALL}")
        sys.exit(2)
    except Exception as e:
        print(f"{Fore.RED}Error: {e}{Style.RESET_ALL}")
        if VERBOSE:
            import traceback
            traceback.print_exc()
        sys.exit(2)


if __name__ == "__main__":
    main()

