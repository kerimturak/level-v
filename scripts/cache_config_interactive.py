#!/usr/bin/env python3
"""
Interactive Cache Configuration Tool for CERES RISC-V
Allows custom way and block size combinations
"""

import math
import sys

def is_power_of_2(n: int) -> bool:
    """Check if number is a power of 2"""
    return n > 0 and (n & (n - 1)) == 0

def calculate_cache_config(capacity_kb: float, way: int, blk_size_bytes: int, xlen: int = 32):
    """
    Calculate and display cache configuration

    Returns: True if valid, False if invalid
    """
    blk_size_bits = blk_size_bytes * 8
    capacity_bits = int(capacity_kb * 1024 * 8)
    size_per_way = capacity_bits // way
    num_sets = size_per_way // blk_size_bits

    # Check if num_sets is power of 2
    valid = is_power_of_2(num_sets)

    # Calculate address breakdown
    offset_width = int(math.log2(blk_size_bytes))
    if valid:
        index_width = int(math.log2(num_sets))
    else:
        index_width = int(math.ceil(math.log2(num_sets)))

    tag_width = xlen - index_width - offset_width

    print(f"\n{'='*80}")
    print(f"Configuration: {capacity_kb:.1f} KB, {way}-way, {blk_size_bytes}-byte blocks")
    print(f"{'='*80}")

    print(f"\nCache Structure:")
    print(f"  Total Capacity:    {capacity_kb:.1f} KB ({capacity_bits} bits, {capacity_bits//8} bytes)")
    print(f"  Associativity:     {way}-way set associative")
    print(f"  Block Size:        {blk_size_bytes} bytes ({blk_size_bits} bits)")
    print(f"  Size per way:      {size_per_way//8} bytes ({size_per_way} bits)")
    print(f"  Number of Sets:    {num_sets} sets", end="")

    if valid:
        print(f" ✓ (2^{int(math.log2(num_sets))})")
    else:
        lower_power = 2 ** int(math.log2(num_sets))
        upper_power = 2 ** int(math.ceil(math.log2(num_sets)))
        print(f" ✗ INVALID!")
        print(f"\n  ⚠️  ERROR: {num_sets} is NOT a power of 2")
        print(f"      2^{int(math.log2(lower_power))} = {lower_power}")
        print(f"      2^{int(math.log2(upper_power))} = {upper_power}")
        print(f"      {num_sets} is between these values!")
        print(f"\n  Problem: With {index_width}-bit index:")
        print(f"    - Can address: 0 to {2**index_width - 1} ({2**index_width} different indices)")
        print(f"    - But only {num_sets} sets exist")
        print(f"    - Indices {num_sets} to {2**index_width - 1} → UNDEFINED BEHAVIOR!")

    print(f"\nAddress Breakdown ({xlen}-bit address):")
    print(f"  ┌─{'─'*tag_width}─┬─{'─'*index_width}─┬─{'─'*offset_width}─┐")
    print(f"  │ TAG ({tag_width:2d}b) │ INDEX ({index_width:2d}b) │ OFFSET ({offset_width:2d}b) │")
    print(f"  └─{'─'*tag_width}─┴─{'─'*index_width}─┴─{'─'*offset_width}─┘")
    print(f"   [{xlen-1}:{index_width+offset_width:2d}]      [{index_width+offset_width-1}:{offset_width:2d}]        [{offset_width-1}:0]")

    print(f"\nBit Field Details:")
    print(f"  TAG:    {tag_width:2d} bits [31:{index_width+offset_width}]  - Identifies unique cache line")
    print(f"  INDEX:  {index_width:2d} bits [{index_width+offset_width-1}:{offset_width}]  - Selects 1 of {num_sets} sets")
    print(f"  OFFSET: {offset_width:2d} bits [{offset_width-1}:0]  - Byte within {blk_size_bytes}-byte block")

    print(f"\nSystemVerilog Configuration:")
    print(f"  localparam int DC_CAPACITY = {int(capacity_kb)} * 1024 * 8;  // {capacity_kb:.1f} KB")
    print(f"  localparam int DC_WAY = {way};")
    print(f"  localparam int DC_SIZE = DC_CAPACITY / DC_WAY;")
    print(f"  localparam int BLK_SIZE = {blk_size_bits};  // {blk_size_bytes} bytes")
    print(f"\n  // Computed in dcache.sv:")
    print(f"  //   NUM_SET = (CACHE_SIZE / BLK_SIZE) = {num_sets}")
    print(f"  //   IDX_WIDTH = $clog2(NUM_SET) = {index_width}")
    print(f"  //   TAG_SIZE = XLEN - IDX_WIDTH - BOFFSET = {tag_width}")

    if not valid:
        print(f"\n{'='*80}")
        print(f"RECOMMENDED ALTERNATIVES:")
        print(f"{'='*80}")

        # Find nearest valid configurations
        lower_sets = 2 ** int(math.log2(num_sets))
        upper_sets = 2 ** int(math.ceil(math.log2(num_sets)))

        lower_capacity = (lower_sets * blk_size_bits * way) / (8 * 1024)
        upper_capacity = (upper_sets * blk_size_bits * way) / (8 * 1024)

        print(f"\nOption 1: Reduce to {lower_capacity:.1f} KB ({lower_sets} sets)")
        print(f"  localparam int DC_CAPACITY = {int(lower_capacity)} * 1024 * 8;")

        print(f"\nOption 2: Increase to {upper_capacity:.1f} KB ({upper_sets} sets)")
        print(f"  localparam int DC_CAPACITY = {int(upper_capacity)} * 1024 * 8;")

    return valid

def generate_table(ways_list, blk_sizes_list, size_range_kb):
    """Generate a table of all combinations"""
    print(f"\n{'='*100}")
    print(f"CACHE CONFIGURATION TABLE")
    print(f"{'='*100}")
    print(f"\nBlock sizes: {blk_sizes_list} bytes")
    print(f"Ways: {ways_list}")
    print(f"Size range: {size_range_kb[0]:.1f} - {size_range_kb[1]:.1f} KB")

    for blk_bytes in blk_sizes_list:
        blk_bits = blk_bytes * 8
        print(f"\n{'-'*100}")
        print(f"Block Size: {blk_bytes} bytes ({blk_bits} bits)")
        print(f"{'-'*100}")
        print(f"{'Size (KB)':>10} | ", end="")
        for way in ways_list:
            print(f"{way}-way Sets".center(15), end=" | ")
        print()
        print(f"{'-'*100}")

        # Generate size range (powers of 2)
        size_kb = size_range_kb[0]
        while size_kb <= size_range_kb[1]:
            if size_kb >= 0.5:  # Skip very small sizes
                print(f"{size_kb:>9.1f}  | ", end="")
                for way in ways_list:
                    capacity_bits = int(size_kb * 1024 * 8)
                    size_per_way = capacity_bits // way
                    num_sets = size_per_way // blk_bits

                    if is_power_of_2(num_sets):
                        print(f"{num_sets:>6} ✓".ljust(15), end=" | ")
                    else:
                        print(f"{num_sets:>6} ✗".ljust(15), end=" | ")
                print()

            # Next size
            if size_kb < 1:
                size_kb *= 2
            else:
                size_kb = 2 ** int(math.ceil(math.log2(size_kb + 1)))

        if size_kb > size_range_kb[1]:
            break

def main():
    print("="*80)
    print(" CERES RISC-V Interactive Cache Configuration Tool")
    print("="*80)

    if len(sys.argv) > 1:
        # Command line mode
        if sys.argv[1] == "table":
            # Generate comprehensive table
            ways = [1, 2, 4, 8]
            blk_sizes = [8, 16, 32, 64]  # bytes
            size_range = [0.5, 64]  # KB

            if len(sys.argv) > 2:
                ways = [int(x) for x in sys.argv[2].split(',')]
            if len(sys.argv) > 3:
                blk_sizes = [int(x) for x in sys.argv[3].split(',')]
            if len(sys.argv) > 4:
                size_range = [float(x) for x in sys.argv[4].split(',')]

            generate_table(ways, blk_sizes, size_range)
        else:
            # Direct calculation
            try:
                capacity_kb = float(sys.argv[1])
                way = int(sys.argv[2]) if len(sys.argv) > 2 else 2
                blk_bytes = int(sys.argv[3]) if len(sys.argv) > 3 else 16

                valid = calculate_cache_config(capacity_kb, way, blk_bytes)
                sys.exit(0 if valid else 1)
            except (ValueError, IndexError):
                print("\nUsage:")
                print(f"  {sys.argv[0]} <capacity_kb> [way] [block_size_bytes]")
                print(f"  {sys.argv[0]} table [ways] [block_sizes] [min,max]")
                print(f"\nExamples:")
                print(f"  {sys.argv[0]} 6 2 16        # Check 6KB, 2-way, 16-byte blocks")
                print(f"  {sys.argv[0]} table          # Full table with defaults")
                print(f"  {sys.argv[0]} table 2,4 16,32 # Table for 2/4-way, 16/32-byte blocks")
                sys.exit(1)
    else:
        # Interactive mode
        print("\nEnter cache configuration (or 'table' for full table, 'quit' to exit):")

        while True:
            try:
                print(f"\n{'-'*80}")
                cmd = input("Command [<capacity_kb> <way> <blk_bytes>] or 'table' or 'quit': ").strip()

                if cmd.lower() in ['quit', 'exit', 'q']:
                    break

                if cmd.lower() == 'table':
                    ways = input("Ways (comma-separated, default: 1,2,4,8): ").strip()
                    blk_sizes = input("Block sizes in bytes (comma-separated, default: 8,16,32,64): ").strip()
                    size_range = input("Size range in KB (min,max, default: 0.5,64): ").strip()

                    ways_list = [int(x) for x in ways.split(',')] if ways else [1, 2, 4, 8]
                    blk_list = [int(x) for x in blk_sizes.split(',')] if blk_sizes else [8, 16, 32, 64]
                    range_list = [float(x) for x in size_range.split(',')] if size_range else [0.5, 64]

                    generate_table(ways_list, blk_list, range_list)
                    continue

                parts = cmd.split()
                if len(parts) < 3:
                    print("Please enter: <capacity_kb> <way> <block_size_bytes>")
                    continue

                capacity_kb = float(parts[0])
                way = int(parts[1])
                blk_bytes = int(parts[2])

                calculate_cache_config(capacity_kb, way, blk_bytes)

            except ValueError as e:
                print(f"Error: Invalid input - {e}")
            except KeyboardInterrupt:
                print("\n\nExiting...")
                break

if __name__ == "__main__":
    main()
