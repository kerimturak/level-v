# CERES RISC-V Cache Configuration Guide

## Summary

This directory contains comprehensive cache configuration tools and references for the CERES RISC-V processor.

### Key Constraint

**Cache set count MUST be a power of 2!**

This is because the set index is extracted directly from the address bits. If the set count is not a power of 2, some index values will map to non-existent sets, causing undefined behavior.

## Generated Files

- **cache_configurations.log** - Complete reference of 494 valid cache configurations
  - Sizes from 0.25 KB to 128 KB
  - Various associativity options (1, 2, 3, 4, 6, 8, 12, 16-way)
  - Different block sizes (4, 8, 16, 32, 64, 128, 256 bytes)

## Tools Available

### 1. Interactive Configuration Tool
```bash
python3 scripts/cache_config_interactive.py <capacity_kb> <way> <block_bytes>

# Examples:
python3 scripts/cache_config_interactive.py 6 2 16   # Check if 6KB, 2-way, 16-byte is valid
python3 scripts/cache_config_interactive.py 8 2 16   # Check 8KB configuration
python3 scripts/cache_config_interactive.py table    # Show complete table
```

### 2. Configuration Calculator
```bash
python3 scripts/cache_config_calculator.py
# Generates detailed report of all valid configurations
```

### 3. Database Generator
```bash
python3 scripts/generate_cache_configs.py
# Regenerates the cache_configurations.log file
```

## Current Issue: 6KB with 2-way, 16-byte blocks

### Problem
```systemverilog
localparam int DC_CAPACITY = 6 * 1024 * 8;  // 49152 bits
localparam int DC_WAY = 2;
localparam int DC_SIZE = DC_CAPACITY / DC_WAY;  // 24576 bits per way

// In dcache.sv:
NUM_SET = (CACHE_SIZE / BLK_SIZE) = 24576 / 128 = 192 sets  ❌ NOT power of 2!
```

**Why 192 is invalid:**
- 192 = 2^7 × 1.5 = 128 × 1.5
- log2(192) = 7.58... (not an integer!)
- With 8-bit index: can address 0-255, but only sets 0-191 exist
- **Indices 192-255 → UNDEFINED BEHAVIOR!**

### Solutions

#### Option A: Use 4 KB (recommended if area-constrained)
```systemverilog
localparam int DC_CAPACITY = 4 * 1024 * 8;  // 4 KB
localparam int DC_WAY = 2;
// → 128 sets (2^7) ✓
// → INDEX: 7 bits, TAG: 21 bits
```

#### Option B: Use 8 KB (recommended for performance) ⭐
```systemverilog
localparam int DC_CAPACITY = 8 * 1024 * 8;  // 8 KB
localparam int DC_WAY = 2;
// → 256 sets (2^8) ✓
// → INDEX: 8 bits, TAG: 20 bits
```

#### Option C: Use 6 KB with 3-way
```systemverilog
localparam int DC_CAPACITY = 6 * 1024 * 8;  // 6 KB
localparam int DC_WAY = 3;                  // Change to 3-way!
localparam int BLK_SIZE = 128;              // 16 bytes
// → 128 sets (2^7) ✓
// → INDEX: 7 bits, TAG: 21 bits
```

**Note:** 3-way associativity is less common and may require LRU implementation changes.

#### Option D: Use 6 KB with 6-way
```systemverilog
localparam int DC_CAPACITY = 6 * 1024 * 8;  // 6 KB
localparam int DC_WAY = 6;                  // Change to 6-way!
localparam int BLK_SIZE = 128;              // 16 bytes
// → 64 sets (2^6) ✓
// → INDEX: 6 bits, TAG: 22 bits
```

## Quick Reference: Valid Configurations (16-byte blocks)

| Size | 1-way | 2-way | 3-way | 4-way | 6-way | 8-way |
|------|-------|-------|-------|-------|-------|-------|
| 1 KB |  64 ✓ |  32 ✓ |   -   |  16 ✓ |   -   |   8 ✓ |
| 2 KB | 128 ✓ |  64 ✓ |   -   |  32 ✓ |   -   |  16 ✓ |
| 3 KB |   -   |   -   |  64 ✓ |   -   |  32 ✓ |   -   |
| 4 KB | 256 ✓ | 128 ✓ |   -   |  64 ✓ |   -   |  32 ✓ |
| **6 KB** |   -   |  **192 ❌** | **128 ✓** |   -   | **64 ✓** |   -   |
| 8 KB | 512 ✓ | 256 ✓ |   -   | 128 ✓ |   -   |  64 ✓ |
| 16 KB | 1024 ✓ | 512 ✓ |   -   | 256 ✓ |   -   | 128 ✓ |

## Address Breakdown

For a 32-bit address with 16-byte (128-bit) cache blocks:

```
┌─────────────┬──────────┬─────────┐
│ TAG         │ INDEX    │ OFFSET  │
└─────────────┴──────────┴─────────┘
 [31:IDX+4]    [IDX+3:4]   [3:0]

OFFSET: 4 bits (byte within 16-byte block)
INDEX:  log2(NUM_SETS) bits
TAG:    32 - INDEX - 4 bits
```

### Examples:

**4 KB, 2-way (128 sets):**
- TAG: 21 bits [31:11]
- INDEX: 7 bits [10:4]
- OFFSET: 4 bits [3:0]

**8 KB, 2-way (256 sets):**
- TAG: 20 bits [31:12]
- INDEX: 8 bits [11:4]
- OFFSET: 4 bits [3:0]

**6 KB, 3-way (128 sets):**
- TAG: 21 bits [31:11]
- INDEX: 7 bits [10:4]
- OFFSET: 4 bits [3:0]

## Mathematical Background

For a cache to have valid addressing:

```
NUM_SETS = CAPACITY_PER_WAY / BLOCK_SIZE
         = (TOTAL_CAPACITY / NUM_WAYS) / BLOCK_SIZE

Must be a power of 2: NUM_SETS = 2^n for some integer n
```

**Why 6 KB fails with 2-way:**
```
6 KB = 6144 bytes = 2^11 × 3
     = 2048 × 3

With 2-way:
  Per way = 3072 bytes = 2^10 × 3

With 16-byte blocks:
  Sets = 3072 / 16 = 192 = 2^6 × 3

The factor of 3 makes it impossible!
```

**Valid cache sizes formula:**
```
CAPACITY = 2^m × BLOCK_SIZE × NUM_WAYS bytes

Where:
  - m is any positive integer (determines number of sets)
  - BLOCK_SIZE should be power of 2
  - NUM_WAYS can be any integer (but powers of 2 are common)
```

## Recommendations

1. **For minimal changes:** Use 8 KB (Option B)
   - Only change one number in ceres_param.sv
   - Still 2-way associative
   - Only +33% size increase from 6 KB

2. **For area savings:** Use 4 KB (Option A)
   - 33% smaller than target
   - May impact hit rate slightly

3. **To keep exactly 6 KB:** Use 3-way or 6-way (Option C/D)
   - Requires verification of LRU/replacement logic
   - Less common associativity

## Testing Your Configuration

```bash
# Verify any configuration before using it:
python3 scripts/cache_config_interactive.py <size_kb> <ways> <block_bytes>

# Example - test current (invalid) config:
python3 scripts/cache_config_interactive.py 6 2 16
# Exit code 1 = invalid

# Example - test recommended 8KB config:
python3 scripts/cache_config_interactive.py 8 2 16
# Exit code 0 = valid ✓
```

## Implementation Notes

The dcache module ([rtl/core/mmu/dcache.sv:34-38](../rtl/core/mmu/dcache.sv#L34-L38)) computes:

```systemverilog
localparam NUM_SET = (CACHE_SIZE / BLK_SIZE) / NUM_WAY;
localparam IDX_WIDTH = $clog2(NUM_SET) == 0 ? 1 : $clog2(NUM_SET);
localparam TAG_SIZE = XLEN - IDX_WIDTH - BOFFSET;
```

**Important:** `$clog2()` rounds UP to the next power of 2. If NUM_SET is not a power of 2:
- `$clog2(192) = 8` (since 2^8 = 256 > 192)
- This creates an 8-bit index that can address 256 sets
- But only 192 sets exist → **hardware bug!**

## See Also

- Full configuration database: [cache_configurations.log](cache_configurations.log)
- Interactive tool: [../scripts/cache_config_interactive.py](../scripts/cache_config_interactive.py)
- Calculator: [../scripts/cache_config_calculator.py](../scripts/cache_config_calculator.py)
