#!/usr/bin/env python3
"""
Comprehensive Cache Configuration Generator
Generates all valid cache configurations and exports to log file
"""

import math
from datetime import datetime

def is_power_of_2(n: int) -> bool:
    """Check if number is a power of 2"""
    return n > 0 and (n & (n - 1)) == 0

def generate_all_configs(
    min_kb=0.25,
    max_kb=128,
    ways=[1, 2, 3, 4, 6, 8, 12, 16],
    blk_sizes=[4, 8, 16, 32, 64, 128, 256],  # bytes
    xlen=32
):
    """
    Generate all valid cache configurations

    Returns: List of valid configurations sorted by size
    """
    configs = []

    # Try all size increments
    size_kb = min_kb
    while size_kb <= max_kb:
        capacity_bits = int(size_kb * 1024 * 8)

        for way in ways:
            if capacity_bits % way != 0:
                continue  # Skip if not evenly divisible

            size_per_way = capacity_bits // way

            for blk_bytes in blk_sizes:
                blk_bits = blk_bytes * 8

                if size_per_way % blk_bits != 0:
                    continue  # Skip if not evenly divisible

                num_sets = size_per_way // blk_bits

                # Only keep if num_sets is power of 2
                if is_power_of_2(num_sets):
                    offset_width = int(math.log2(blk_bytes))
                    index_width = int(math.log2(num_sets))
                    tag_width = xlen - index_width - offset_width

                    configs.append({
                        'capacity_kb': size_kb,
                        'capacity_bits': capacity_bits,
                        'capacity_bytes': capacity_bits // 8,
                        'way': way,
                        'blk_bytes': blk_bytes,
                        'blk_bits': blk_bits,
                        'num_sets': num_sets,
                        'size_per_way': size_per_way // 8,  # in bytes
                        'offset_width': offset_width,
                        'index_width': index_width,
                        'tag_width': tag_width,
                    })

        # Increment size (use finer granularity for small sizes)
        if size_kb < 1:
            size_kb += 0.25
        elif size_kb < 4:
            size_kb += 0.5
        elif size_kb < 16:
            size_kb += 1
        else:
            size_kb += 2

    return sorted(configs, key=lambda x: (x['capacity_kb'], x['way'], x['blk_bytes']))

def write_log_file(configs, filename='cache_configs.log'):
    """Write configurations to a detailed log file"""

    with open(filename, 'w') as f:
        # Header
        f.write('='*100 + '\n')
        f.write('CERES RISC-V CACHE CONFIGURATION REFERENCE\n')
        f.write('='*100 + '\n')
        f.write(f'Generated: {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}\n')
        f.write(f'Total valid configurations: {len(configs)}\n')
        f.write('='*100 + '\n\n')

        # Summary statistics
        f.write('SUMMARY STATISTICS:\n')
        f.write('-'*100 + '\n')
        sizes = sorted(set(c['capacity_kb'] for c in configs))
        f.write(f'Size range: {sizes[0]:.2f} KB to {sizes[-1]:.2f} KB\n')
        f.write(f'Number of unique sizes: {len(sizes)}\n')

        ways_used = sorted(set(c['way'] for c in configs))
        f.write(f'Ways available: {", ".join(map(str, ways_used))}\n')

        blks_used = sorted(set(c['blk_bytes'] for c in configs))
        f.write(f'Block sizes: {", ".join(str(b) + " bytes" for b in blks_used)}\n')
        f.write('\n\n')

        # Detailed table
        f.write('='*100 + '\n')
        f.write('COMPLETE CONFIGURATION TABLE\n')
        f.write('='*100 + '\n\n')

        # Group by cache size
        current_size = None
        config_num = 0

        for config in configs:
            if config['capacity_kb'] != current_size:
                current_size = config['capacity_kb']
                f.write('\n' + '='*100 + '\n')
                f.write(f'CACHE SIZE: {current_size:.2f} KB ({config["capacity_bytes"]} bytes)\n')
                f.write('='*100 + '\n\n')

            config_num += 1

            f.write(f'Configuration #{config_num}:\n')
            f.write('-'*100 + '\n')
            f.write(f'  Capacity:        {config["capacity_kb"]:.2f} KB ({config["capacity_bytes"]} bytes = {config["capacity_bits"]} bits)\n')
            f.write(f'  Associativity:   {config["way"]}-way set associative\n')
            f.write(f'  Block Size:      {config["blk_bytes"]} bytes ({config["blk_bits"]} bits)\n')
            f.write(f'  Number of Sets:  {config["num_sets"]} (2^{config["index_width"]})\n')
            f.write(f'  Size per Way:    {config["size_per_way"]} bytes\n')
            f.write(f'\n')
            f.write(f'  Address Breakdown (32-bit):\n')
            f.write(f'    TAG:    {config["tag_width"]:2d} bits  [{31}:{config["index_width"]+config["offset_width"]}]\n')
            f.write(f'    INDEX:  {config["index_width"]:2d} bits  [{config["index_width"]+config["offset_width"]-1}:{config["offset_width"]}]  (selects 1 of {config["num_sets"]} sets)\n')
            f.write(f'    OFFSET: {config["offset_width"]:2d} bits  [{config["offset_width"]-1}:0]  (byte within {config["blk_bytes"]}-byte block)\n')
            f.write(f'\n')
            f.write(f'  SystemVerilog Code:\n')
            f.write(f'    localparam int DC_CAPACITY = {int(config["capacity_kb"] * 1024 * 8)};  // {config["capacity_kb"]:.2f} KB\n')
            f.write(f'    localparam int DC_WAY = {config["way"]};\n')
            f.write(f'    localparam int DC_SIZE = DC_CAPACITY / DC_WAY;\n')
            f.write(f'    localparam int BLK_SIZE = {config["blk_bits"]};  // {config["blk_bytes"]} bytes\n')
            f.write(f'    // Results: NUM_SET={config["num_sets"]}, IDX_WIDTH={config["index_width"]}, TAG_SIZE={config["tag_width"]}\n')
            f.write(f'\n')

        # Quick reference tables
        f.write('\n\n' + '='*100 + '\n')
        f.write('QUICK REFERENCE TABLES\n')
        f.write('='*100 + '\n\n')

        # Table by size and way for fixed block size
        for blk_bytes in [16, 32]:  # Common block sizes
            f.write(f'\n{"-"*100}\n')
            f.write(f'Block Size: {blk_bytes} bytes ({blk_bytes*8} bits)\n')
            f.write(f'{"-"*100}\n')
            f.write(f'{"Size (KB)":>10} | ')

            ways_for_table = [1, 2, 3, 4, 6, 8]
            for way in ways_for_table:
                f.write(f'{way}-way Sets'.center(15) + ' | ')
            f.write('\n' + '-'*100 + '\n')

            for size_kb in sorted(set(c['capacity_kb'] for c in configs)):
                if size_kb > 32:  # Limit table size
                    continue

                f.write(f'{size_kb:>9.2f}  | ')

                for way in ways_for_table:
                    # Find matching config
                    matching = [c for c in configs
                               if c['capacity_kb'] == size_kb
                               and c['way'] == way
                               and c['blk_bytes'] == blk_bytes]

                    if matching:
                        c = matching[0]
                        f.write(f'{c["num_sets"]:>6} ✓'.ljust(15) + ' | ')
                    else:
                        f.write(' '*15 + ' | ')

                f.write('\n')

        # Special section for common configurations
        f.write('\n\n' + '='*100 + '\n')
        f.write('COMMON RECOMMENDED CONFIGURATIONS\n')
        f.write('='*100 + '\n\n')

        common = [
            (2, 2, 16, 'Small embedded systems'),
            (4, 2, 16, 'Minimal cache'),
            (8, 2, 16, 'Standard small cache'),
            (16, 4, 16, 'Medium cache'),
            (32, 4, 32, 'Large cache'),
        ]

        for size_kb, way, blk_bytes, desc in common:
            matching = [c for c in configs
                       if c['capacity_kb'] == size_kb
                       and c['way'] == way
                       and c['blk_bytes'] == blk_bytes]

            if matching:
                c = matching[0]
                f.write(f'{desc}:\n')
                f.write(f'  {size_kb} KB, {way}-way, {blk_bytes}-byte blocks → {c["num_sets"]} sets\n')
                f.write(f'  DC_CAPACITY = {int(size_kb)} * 1024 * 8;  DC_WAY = {way};  BLK_SIZE = {blk_bytes*8};\n')
                f.write(f'\n')

def main():
    print("="*80)
    print("Generating comprehensive cache configuration database...")
    print("="*80)

    # Generate all configurations
    print("\nGenerating configurations...")
    configs = generate_all_configs(
        min_kb=0.25,
        max_kb=128,
        ways=[1, 2, 3, 4, 6, 8, 12, 16],
        blk_sizes=[4, 8, 16, 32, 64, 128, 256],
    )

    print(f"Found {len(configs)} valid configurations")

    # Write to log file
    log_file = '/home/kerim/level-v/docs/cache_configurations.log'
    print(f"\nWriting to {log_file}...")
    write_log_file(configs, log_file)

    print(f"✓ Complete! Log file created with {len(configs)} configurations")

    # Print summary
    print("\n" + "="*80)
    print("SUMMARY")
    print("="*80)

    sizes = sorted(set(c['capacity_kb'] for c in configs))
    print(f"\nSize range: {sizes[0]:.2f} KB to {sizes[-1]:.2f} KB")
    print(f"Unique sizes: {len(sizes)}")

    # Show configurations for 6KB specifically
    configs_6kb = [c for c in configs if abs(c['capacity_kb'] - 6.0) < 0.01]
    print(f"\n6KB configurations available: {len(configs_6kb)}")
    if configs_6kb:
        print("  Valid 6KB options:")
        for c in configs_6kb[:5]:  # Show first 5
            print(f"    {c['way']}-way, {c['blk_bytes']}-byte blocks → {c['num_sets']} sets")
        if len(configs_6kb) > 5:
            print(f"    ... and {len(configs_6kb)-5} more")

    # Show nearest to 6KB with 2-way, 16-byte
    print("\n2-way, 16-byte configurations near 6KB:")
    nearby = [c for c in configs
              if c['way'] == 2 and c['blk_bytes'] == 16
              and 4 <= c['capacity_kb'] <= 8]
    for c in nearby:
        print(f"  {c['capacity_kb']:.0f} KB → {c['num_sets']} sets")

    print(f"\nComplete configuration reference written to:")
    print(f"  {log_file}")

if __name__ == "__main__":
    main()
