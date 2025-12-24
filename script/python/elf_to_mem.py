#!/usr/bin/env python3
"""
ELF/binary -> .mem converter for block-based RAM initialization.
Generates one hex line per block (default 16 bytes / 128 bits) suitable
for `$readmemh` in your `wrapper_ram.sv` where `ram` elements are
`BLK_SIZE` bits.

Usage examples:
  # after building test.elf linked at 0x80000000
  riscv32-unknown-elf-objcopy -O binary test.elf test.bin
  ./tools/elf_to_mem.py --in test.bin --out rv32uc-p-rvc.mem --addr 0x80000000 \
      --block-bytes 16 --word-size 4 --word-endian little --word-order high-to-low

Options:
  --in: input binary file
  --out: output .mem file
  --addr: base address where the binary is linked (0x80000000 default)
  --block-bytes: block size in bytes (default 16)
  --word-size: word size in bytes (default 4)
  --word-endian: how to interpret bytes within each word when formatting (little|big)
  --word-order: how to order words within the printed block (high-to-low | low-to-high)

If formats don't match your simulator, try switching `--word-endian` and `--word-order`.
"""

import argparse
import struct
from pathlib import Path

parser = argparse.ArgumentParser(description="Convert bin -> .mem (block hex lines)")
parser.add_argument('--in', dest='infile', required=True, help='Input binary file (raw)')
parser.add_argument('--out', dest='outfile', required=True, help='Output .mem file')
parser.add_argument('--addr', dest='base_addr', default='0x80000000', help='Link base address (not used for content, informational)')
parser.add_argument('--block-bytes', dest='block_bytes', type=int, default=16, help='Bytes per .mem line (block size)')
parser.add_argument('--word-size', dest='word_size', type=int, default=4, help='Word size (bytes) inside each block')
parser.add_argument('--word-endian', dest='word_endian', choices=['little','big'], default='little', help='Byte order inside each word')
parser.add_argument('--word-order', dest='word_order', choices=['high-to-low','low-to-high'], default='high-to-low', help='Order of words when printing block (which word is printed first)')
parser.add_argument('--pad', dest='pad_byte', type=lambda x: int(x,0), default=0x00, help='Pad byte value')
parser.add_argument('--pad-to-size', dest='pad_to_size', type=lambda x: int(x,0), default=0, help='Pad output to minimum size (bytes). For heap/stack allocation.')
args = parser.parse_args()

infile = Path(args.infile)
outfile = Path(args.outfile)
block_bytes = args.block_bytes
word_size = args.word_size
if block_bytes % word_size != 0:
    raise SystemExit('block-bytes must be a multiple of word-size')
words_per_block = block_bytes // word_size

# read input binary
data = infile.read_bytes()

# pad to minimum size if specified (for heap/stack)
if args.pad_to_size > 0 and len(data) < args.pad_to_size:
    data = data + bytes([args.pad_byte]) * (args.pad_to_size - len(data))

# pad to block boundary
if len(data) % block_bytes != 0:
    pad_len = block_bytes - (len(data) % block_bytes)
    data = data + bytes([args.pad_byte]) * pad_len

lines = []
for i in range(0, len(data), block_bytes):
    block = data[i:i+block_bytes]
    words = []
    for w in range(words_per_block):
        start = w*word_size
        wbytes = block[start:start+word_size]
        if args.word_endian == 'little':
            # interpret as little-endian integer
            val = int.from_bytes(wbytes, 'little')
        else:
            val = int.from_bytes(wbytes, 'big')
        words.append(val)
    # choose print order
    if args.word_order == 'high-to-low':
        ordered = list(reversed(words))
    else:
        ordered = words
    # format each word as 2*word_size hex digits, concatenate
    fmt = ''.join(f"{w:0{word_size*2}x}" for w in ordered)
    lines.append(fmt)

# write output
outfile.parent.mkdir(parents=True, exist_ok=True)
with outfile.open('w') as f:
    for ln in lines:
        f.write(ln + '\n')

print(f'Wrote {len(lines)} lines to {outfile} (block {block_bytes} bytes, word {word_size} bytes)')
