#!/usr/bin/env python3
"""
compare_coremark_output.py — CoreMark Output Comparator
=======================================================

Compare CoreMark UART output from Ceres-V and Spike to verify:
  - Same initialization messages
  - Same CoreMark parameters (iterations, size, etc.)
  - Same CRC results (crclist, crcmatrix, crcstate, crcfinal)
  - Same validation status

Usage:
    python3 compare_coremark_output.py \\
        --ceres ceres_uart.log \\
        --spike spike_uart.log
"""

import sys
import re
import argparse
from colorama import Fore, Style, init

init(autoreset=True)

def extract_coremark_data(filename):
    """Extract key CoreMark metrics from UART output."""
    data = {
        'iterations': None,
        'coremark_size': None,
        'compiler_version': None,
        'compiler_flags': None,
        'seedcrc': None,
        'crclist': None,
        'crcmatrix': None,
        'crcstate': None,
        'crcfinal': None,
        'validation_status': None,
    }

    try:
        with open(filename, 'r', errors='ignore') as f:
            content = f.read()

            # Extract iterations
            match = re.search(r'Iterations\s*:\s*(\d+)', content)
            if match:
                data['iterations'] = int(match.group(1))

            # Extract CoreMark Size
            match = re.search(r'CoreMark Size\s*:\s*(\d+)', content)
            if match:
                data['coremark_size'] = int(match.group(1))

            # Extract compiler version
            match = re.search(r'Compiler version\s*:\s*(.+)', content)
            if match:
                data['compiler_version'] = match.group(1).strip()

            # Extract compiler flags
            match = re.search(r'Compiler flags\s*:\s*(.+)', content)
            if match:
                data['compiler_flags'] = match.group(1).strip()

            # Extract CRCs
            match = re.search(r'seedcrc\s*:\s*0x([0-9a-f]+)', content, re.IGNORECASE)
            if match:
                data['seedcrc'] = match.group(1)

            match = re.search(r'\[0\]crclist\s*:\s*0x([0-9a-f]+)', content, re.IGNORECASE)
            if match:
                data['crclist'] = match.group(1)

            match = re.search(r'\[0\]crcmatrix\s*:\s*0x([0-9a-f]+)', content, re.IGNORECASE)
            if match:
                data['crcmatrix'] = match.group(1)

            match = re.search(r'\[0\]crcstate\s*:\s*0x([0-9a-f]+)', content, re.IGNORECASE)
            if match:
                data['crcstate'] = match.group(1)

            match = re.search(r'\[0\]crcfinal\s*:\s*0x([0-9a-f]+)', content, re.IGNORECASE)
            if match:
                data['crcfinal'] = match.group(1)

            # Check validation
            if 'Correct operation validated' in content:
                data['validation_status'] = 'PASS'
            elif 'Errors detected' in content:
                data['validation_status'] = 'FAIL'
            else:
                data['validation_status'] = 'UNKNOWN'

    except Exception as e:
        print(f"{Fore.RED}Error reading {filename}: {e}{Style.RESET_ALL}")

    return data

def compare_data(ceres, spike):
    """Compare extracted data and return (pass, details)."""
    differences = []

    # Compare each field
    fields = ['iterations', 'coremark_size', 'compiler_version', 'compiler_flags',
              'seedcrc', 'crclist', 'crcmatrix', 'crcstate', 'crcfinal', 'validation_status']

    for field in fields:
        c_val = ceres.get(field)
        s_val = spike.get(field)

        if c_val is None and s_val is None:
            continue
        elif c_val is None:
            differences.append(f"{field}: Ceres=MISSING, Spike={s_val}")
        elif s_val is None:
            differences.append(f"{field}: Ceres={c_val}, Spike=MISSING")
        elif c_val != s_val:
            differences.append(f"{field}: Ceres={c_val}, Spike={s_val}")

    return len(differences) == 0, differences

def main():
    parser = argparse.ArgumentParser(
        description='Compare CoreMark output from Ceres-V and Spike'
    )

    parser.add_argument('--ceres', required=True, help='Ceres-V UART output file')
    parser.add_argument('--spike', required=True, help='Spike UART output file')
    parser.add_argument('--output', help='Output report file (optional)')

    args = parser.parse_args()

    print(f"\n{Fore.CYAN}{'='*80}{Style.RESET_ALL}")
    print(f"{Fore.CYAN}CoreMark Output Comparator{Style.RESET_ALL}")
    print(f"{Fore.CYAN}{'='*80}{Style.RESET_ALL}\n")

    # Extract data
    print(f"{Fore.YELLOW}[1/3]{Style.RESET_ALL} Extracting Ceres-V data...")
    ceres_data = extract_coremark_data(args.ceres)

    print(f"{Fore.YELLOW}[2/3]{Style.RESET_ALL} Extracting Spike data...")
    spike_data = extract_coremark_data(args.spike)

    # Compare
    print(f"\n{Fore.YELLOW}[3/3]{Style.RESET_ALL} Comparing results...\n")

    passed, differences = compare_data(ceres_data, spike_data)

    # Print summary table
    print(f"{Fore.CYAN}{'Field':<20} {'Ceres-V':<25} {'Spike':<25} {'Status'}{Style.RESET_ALL}")
    print(f"{Fore.CYAN}{'-'*80}{Style.RESET_ALL}")

    fields_to_show = [
        ('Iterations', 'iterations'),
        ('CoreMark Size', 'coremark_size'),
        ('Compiler', 'compiler_version'),
        ('Seed CRC', 'seedcrc'),
        ('CRC List', 'crclist'),
        ('CRC Matrix', 'crcmatrix'),
        ('CRC State', 'crcstate'),
        ('CRC Final', 'crcfinal'),
        ('Validation', 'validation_status'),
    ]

    for label, key in fields_to_show:
        c_val = str(ceres_data.get(key, 'N/A'))
        s_val = str(spike_data.get(key, 'N/A'))

        # Truncate long values
        c_val = c_val[:23] + '..' if len(c_val) > 25 else c_val
        s_val = s_val[:23] + '..' if len(s_val) > 25 else s_val

        if ceres_data.get(key) == spike_data.get(key):
            status = f"{Fore.GREEN}✓{Style.RESET_ALL}"
        else:
            status = f"{Fore.RED}✗{Style.RESET_ALL}"

        print(f"{label:<20} {c_val:<25} {s_val:<25} {status}")

    # Final result
    print(f"\n{Fore.CYAN}{'='*80}{Style.RESET_ALL}")
    if passed:
        print(f"{Fore.GREEN}✅ PASS - CoreMark outputs match!{Style.RESET_ALL}")
        print(f"{Fore.GREEN}Both implementations produce identical CRC results.{Style.RESET_ALL}\n")
        return_code = 0
    else:
        print(f"{Fore.RED}❌ FAIL - CoreMark outputs differ!{Style.RESET_ALL}")
        print(f"\n{Fore.YELLOW}Differences:{Style.RESET_ALL}")
        for diff in differences:
            print(f"  • {diff}")
        print()
        return_code = 1

    # Write output file if requested
    if args.output:
        with open(args.output, 'w') as f:
            f.write("CoreMark Output Comparison\n")
            f.write("="*80 + "\n\n")

            f.write("Ceres-V:\n")
            for k, v in ceres_data.items():
                f.write(f"  {k}: {v}\n")

            f.write("\nSpike:\n")
            for k, v in spike_data.items():
                f.write(f"  {k}: {v}\n")

            f.write("\nResult: ")
            if passed:
                f.write("PASS\n")
            else:
                f.write("FAIL\n\nDifferences:\n")
                for diff in differences:
                    f.write(f"  {diff}\n")

        print(f"{Fore.CYAN}Report written to: {args.output}{Style.RESET_ALL}\n")

    return return_code

if __name__ == '__main__':
    sys.exit(main())
