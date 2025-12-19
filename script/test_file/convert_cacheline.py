#!/usr/bin/env python3
"""
Convert 32-bit hex/mem file to cache-line formatted mem file
Each input line contains one 32-bit word (8 hex characters)
Output lines contain multiple words based on cache line size
"""

import sys
import os

def convert_to_cacheline(input_file, output_file, words_per_line):
    """
    Convert input hex/mem file to cache-line format

    Args:
        input_file: Input file with 32-bit words (one per line)
        output_file: Output file with cache-line formatted data
        words_per_line: Number of 32-bit words per cache line
    """

    if not os.path.exists(input_file):
        print(f"Error: Input file '{input_file}' not found!")
        sys.exit(1)

    try:
        words_per_line = int(words_per_line)
        if words_per_line <= 0:
            raise ValueError("Words per line must be positive")
    except ValueError as e:
        print(f"Error: Invalid words_per_line value: {e}")
        sys.exit(1)

    words = []
    line_count = 0

    # Read input file
    print(f"Reading from: {input_file}")
    with open(input_file, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#') or line.startswith('//'):
                continue

            # Remove any non-hex characters (spaces, comments, etc.)
            # Take only the hex part
            hex_data = ''.join(c for c in line.split()[0] if c in '0123456789abcdefABCDEF')

            if hex_data:
                # Ensure it's 8 characters (32 bits)
                if len(hex_data) > 8:
                    hex_data = hex_data[:8]
                elif len(hex_data) < 8:
                    hex_data = hex_data.zfill(8)

                words.append(hex_data)
                line_count += 1

    print(f"Read {line_count} words from input file")

    # Pad to complete cache line if needed
    remainder = len(words) % words_per_line
    if remainder != 0:
        padding_needed = words_per_line - remainder
        print(f"Padding with {padding_needed} zero words to complete last cache line")
        words.extend(['00000000'] * padding_needed)

    # Write output file
    print(f"Writing to: {output_file}")
    cache_lines = 0
    with open(output_file, 'w') as f:
        for i in range(0, len(words), words_per_line):
            cache_line = words[i:i + words_per_line]
            # Concatenate words in reverse order (little-endian: first word = least significant = rightmost)
            line_data = ''.join(reversed(cache_line))
            f.write(line_data + '\n')
            cache_lines += 1

    print(f"Wrote {cache_lines} cache lines ({cache_lines * words_per_line} words)")
    print(f"Cache line format: {words_per_line} words/line = {words_per_line * 4} bytes/line")

if __name__ == '__main__':
    if len(sys.argv) != 4:
        print("Usage: convert_cacheline.py <input_file> <output_file> <words_per_line>")
        print("  input_file      - Input hex/mem file with 32-bit words")
        print("  output_file     - Output cache-line formatted mem file")
        print("  words_per_line  - Number of 32-bit words per cache line")
        sys.exit(1)

    input_file = sys.argv[1]
    output_file = sys.argv[2]
    words_per_line = sys.argv[3]

    convert_to_cacheline(input_file, output_file, words_per_line)
