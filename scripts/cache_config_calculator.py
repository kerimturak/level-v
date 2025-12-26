#!/usr/bin/env python3
"""
Cache Configuration Calculator for CERES RISC-V
Calculates valid cache configurations where NUM_SET is a power of 2
"""

import math
from typing import List, Tuple

def is_power_of_2(n: int) -> bool:
    """Check if number is a power of 2"""
    return n > 0 and (n & (n - 1)) == 0

def calculate_cache_params(capacity_kb: float, way: int, blk_size_bits: int = 128, xlen: int = 32):
    """
    Calculate cache parameters

    Args:
        capacity_kb: Total cache capacity in KB
        way: Number of ways (associativity)
        blk_size_bits: Block size in bits (default: 128)
        xlen: Address width in bits (default: 32)

    Returns:
        Dictionary with cache parameters or None if invalid
    """
    capacity_bits = int(capacity_kb * 1024 * 8)
    size_per_way = capacity_bits // way
    num_sets = size_per_way // blk_size_bits

    # Check if num_sets is power of 2
    if not is_power_of_2(num_sets):
        return None

    # Calculate address breakdown
    offset_width = int(math.log2(blk_size_bits // 8))
    index_width = int(math.log2(num_sets))
    tag_width = xlen - index_width - offset_width

    return {
        'capacity_kb': capacity_kb,
        'capacity_bits': capacity_bits,
        'capacity_bytes': capacity_bits // 8,
        'way': way,
        'size_per_way_bits': size_per_way,
        'size_per_way_bytes': size_per_way // 8,
        'num_sets': num_sets,
        'blk_size_bits': blk_size_bits,
        'blk_size_bytes': blk_size_bits // 8,
        'offset_width': offset_width,
        'index_width': index_width,
        'tag_width': tag_width,
        'total_addr_bits': offset_width + index_width + tag_width
    }

def print_config(config: dict):
    """Pretty print a cache configuration"""
    print(f"\n{'='*80}")
    print(f"Capacity: {config['capacity_kb']:.1f} KB ({config['capacity_bytes']} bytes)")
    print(f"Ways: {config['way']}-way set associative")
    print(f"Sets: {config['num_sets']} sets (2^{config['index_width']})")
    print(f"Block Size: {config['blk_size_bytes']} bytes ({config['blk_size_bits']} bits)")
    print(f"-" * 80)
    print(f"Size per way: {config['size_per_way_bytes']} bytes ({config['size_per_way_bits']} bits)")
    print(f"\nAddress Breakdown ({config['total_addr_bits']}-bit):")
    print(f"  TAG:    {config['tag_width']:2d} bits [31:{config['index_width']+config['offset_width']}]")
    print(f"  INDEX:  {config['index_width']:2d} bits [{config['index_width']+config['offset_width']-1}:{config['offset_width']}]  (selects 1 of {config['num_sets']} sets)")
    print(f"  OFFSET: {config['offset_width']:2d} bits [{config['offset_width']-1}:0]  (byte within {config['blk_size_bytes']}-byte block)")
    print(f"\nSystemVerilog Parameter:")
    print(f"  localparam int DC_CAPACITY = {int(config['capacity_kb'])} * 1024 * 8;  // {config['capacity_kb']:.1f} KB")
    print(f"  localparam int DC_WAY = {config['way']};")
    print(f"  localparam int DC_SIZE = DC_CAPACITY / DC_WAY;")
    print(f"  // Results in:")
    print(f"  //   NUM_SET = {config['num_sets']}")
    print(f"  //   IDX_WIDTH = {config['index_width']}")
    print(f"  //   TAG_SIZE = {config['tag_width']}")

def generate_valid_configs(
    min_kb: float = 0.5,
    max_kb: float = 64,
    ways: List[int] = [1, 2, 4, 8],
    blk_size_bits: int = 128
) -> List[dict]:
    """
    Generate all valid cache configurations within size range

    Args:
        min_kb: Minimum cache size in KB
        max_kb: Maximum cache size in KB
        ways: List of associativity options
        blk_size_bits: Block size in bits

    Returns:
        List of valid configurations sorted by size
    """
    valid_configs = []

    # Generate potential sizes (powers of 2 in bytes)
    min_bytes = int(min_kb * 1024)
    max_bytes = int(max_kb * 1024)

    # Start from minimum power of 2
    size_bytes = 2 ** int(math.log2(min_bytes))

    while size_bytes <= max_bytes:
        size_kb = size_bytes / 1024

        for way in ways:
            config = calculate_cache_params(size_kb, way, blk_size_bits)
            if config is not None:
                valid_configs.append(config)

        size_bytes *= 2  # Next power of 2

    return sorted(valid_configs, key=lambda x: (x['capacity_kb'], x['way']))

def main():
    print("="*80)
    print(" CERES RISC-V Cache Configuration Calculator")
    print("="*80)

    BLK_SIZE = 128  # bits
    XLEN = 32

    print(f"\nFixed Parameters:")
    print(f"  Block Size: {BLK_SIZE} bits ({BLK_SIZE//8} bytes)")
    print(f"  Address Width: {XLEN} bits")

    # Generate configurations
    print(f"\n{'='*80}")
    print(" VALID CACHE CONFIGURATIONS")
    print(f"{'='*80}")

    # Common configurations
    configs = generate_valid_configs(
        min_kb=1,
        max_kb=32,
        ways=[1, 2, 4, 8],
        blk_size_bits=BLK_SIZE
    )

    print(f"\nFound {len(configs)} valid configurations:\n")

    # Group by size for easier reading
    current_size = None
    for config in configs:
        if config['capacity_kb'] != current_size:
            current_size = config['capacity_kb']
            print(f"\n{'-'*80}")
            print(f"Cache Size: {current_size:.1f} KB")
            print(f"{'-'*80}")

        print(f"  {config['way']}-way: {config['num_sets']:4d} sets "
              f"(idx={config['index_width']}b, tag={config['tag_width']}b) "
              f"→ DC_CAPACITY = {int(config['capacity_kb'])} * 1024 * 8")

    # Show current invalid configuration
    print(f"\n{'='*80}")
    print(" CURRENT CONFIGURATION (INVALID!)")
    print(f"{'='*80}")

    invalid_config = calculate_cache_params(6.0, 2, BLK_SIZE)
    if invalid_config is None:
        # Manually calculate to show the problem
        capacity_bits = 6 * 1024 * 8
        size_per_way = capacity_bits // 2
        num_sets = size_per_way // BLK_SIZE

        print(f"\nCapacity: 6 KB")
        print(f"Ways: 2-way")
        print(f"Sets: {num_sets} sets ❌ NOT a power of 2!")
        print(f"  2^7 = 128")
        print(f"  2^8 = 256")
        print(f"  192 is between these, causing undefined behavior for indices 192-255")

        print(f"\n⚠️  RECOMMENDATION: Use 8 KB (256 sets) or 4 KB (128 sets) instead")

    # Detailed view of recommended configurations
    print(f"\n{'='*80}")
    print(" RECOMMENDED CONFIGURATIONS (closest to 6KB)")
    print(f"{'='*80}")

    recommended = [
        calculate_cache_params(4.0, 2, BLK_SIZE),  # 4KB
        calculate_cache_params(8.0, 2, BLK_SIZE),  # 8KB
    ]

    for config in recommended:
        if config:
            print_config(config)

    # Show different block sizes
    print(f"\n{'='*80}")
    print(" CONFIGURATIONS WITH DIFFERENT BLOCK SIZES (6KB, 2-way)")
    print(f"{'='*80}")

    for blk_bits in [64, 128, 256, 512]:
        config = calculate_cache_params(6.0, 2, blk_bits)
        blk_bytes = blk_bits // 8
        if config:
            print(f"  ✓ Block size {blk_bytes:3d} bytes: {config['num_sets']:4d} sets (valid)")
        else:
            capacity_bits = 6 * 1024 * 8
            size_per_way = capacity_bits // 2
            num_sets = size_per_way // blk_bits
            print(f"  ✗ Block size {blk_bytes:3d} bytes: {num_sets:4d} sets (invalid - not power of 2)")

if __name__ == "__main__":
    main()
