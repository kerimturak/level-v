#!/usr/bin/env python3
"""
Convert 32-bit word HEX file to 128-bit cache line MEM file for synthesis.

Input:  32-bit words (one per line, hex)
Output: 128-bit cache lines (4 words packed, little-endian word order)

Usage:
    python3 hex32_to_mem128.py input.hex output.mem

Example:
    Input (32-bit words):
        00000000
        41014081
        42014181
        43014281

    Output (128-bit cache line):
        43014281420141814101408100000000

Note: Words are packed in reverse order (word3 word2 word1 word0) to match
      little-endian byte ordering in cache lines.
"""

import sys
from pathlib import Path


def hex32_to_mem128(input_file: Path, output_file: Path) -> None:
    """Convert 32-bit HEX to 128-bit MEM format."""

    # Read all 32-bit words
    lines = input_file.read_text().splitlines()
    words = [line.strip() for line in lines if line.strip()]

    # Pack every 4 words into 128-bit cache lines
    mem_lines = []
    for i in range(0, len(words), 4):
        # Get 4 words (pad with zeros if needed)
        group = words[i:i+4]
        while len(group) < 4:
            group.append("00000000")

        # Pack in reverse order: word[3] word[2] word[1] word[0]
        # This matches little-endian word ordering
        cache_line = "".join(reversed(group))
        mem_lines.append(cache_line.lower())

    # Write output
    output_file.write_text("\n".join(mem_lines) + "\n")

    print(f"✅ Converted {len(words)} words → {len(mem_lines)} cache lines")
    print(f"   Input:  {input_file}")
    print(f"   Output: {output_file}")


def main():
    if len(sys.argv) != 3:
        print("Usage: python3 hex32_to_mem128.py input.hex output.mem")
        sys.exit(1)

    input_path = Path(sys.argv[1])
    output_path = Path(sys.argv[2])

    if not input_path.exists():
        print(f"❌ Error: Input file not found: {input_path}")
        sys.exit(1)

    hex32_to_mem128(input_path, output_path)


if __name__ == "__main__":
    main()
