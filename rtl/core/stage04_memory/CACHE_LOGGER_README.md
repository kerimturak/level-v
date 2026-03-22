# Cache logger user guide

## Overview

`cache_logger.sv` is a debug helper that logs every request into the memory-stage unified cache and every response, in a tabular text format.

## Features

### Logged fields

**Request**

- **Time**: Request time (ns)
- **Valid**: Whether the request is valid
- **Address**: Memory address (hex)
- **Operation**: READ or WRITE
- **Size**: Transfer size (1B, 2B, 4B)
- **Write data**: Data written on stores (hex)
- **Uncached**: Uncached access flag

**Response**

- **Time**: Response time (ns)
- **Valid**: Whether the response is valid
- **Miss/Hit**: Cache miss or hit
- **Ready**: Whether the cache is ready
- **Read data**: Data returned on loads (hex)

## Usage

### 1. Verilator simulation

Enable cache logs:

```bash
make verilate LOG_CACHE=1
make run:your_test LOG_CACHE=1
```

### 2. Example commands

```bash
# ISA test with cache log
make run:rv32ui-p-add LOG_CACHE=1

# CoreMark with cache log
make run_coremark SIM_FAST=1 TRACE=0 LOG_CACHE=1

# Custom program
make verilate LOG_CACHE=1
./build/obj_dir/Vlevel_wrapper +firmware=your_program.hex
```

### 3. Combining with other logs

```bash
# Cache + commit trace
make run:rv32ui-p-add LOG_CACHE=1 LOG_COMMIT=1

# Cache + UART + RAM
make run:your_test LOG_CACHE=1 LOG_UART=1 LOG_RAM=1

# Verbose bundle
make run:your_test LOG_CACHE=1 LOG_COMMIT=1 LOG_UART=1 LOG_RAM=1 LOG_BP=1
```

## Output format

```
╔═══════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                         CACHE TRANSACTION LOG                                                         ║
╠═════════╦═══════════╦════════════╦═════════╦═════════╦═══════════════╦═══════════════════════════════════════════════╣
║  Time   ║    REQ    ║  Address   ║  Op     ║  Size   ║  Write Data   ║                RESPONSE                       ║
║   (ns)  ║  Valid    ║   (hex)    ║ (R/W)   ║ (bytes) ║     (hex)     ║  Valid  │  Miss  │  Ready  │   Read Data      ║
╠═════════╬═══════════╬════════════╬═════════╬═════════╬═══════════════╬═════════╪════════╪═════════╪══════════════════╣
║    1500 ║     1     ║ 0x80000000 ║ READ    ║  4B     ║       -       ║    -    │   -    │    -    │        -         ║
║    1520 ║     -     ║     -      ║    -    ║    -    ║       -       ║    1    │  MISS  │  YES   │  0x00000013      ║
║    1540 ║     1     ║ 0x80000004 ║ WRITE   ║  4B     ║  0xdeadbeef   ║    -    │   -    │    -    │        -         ║
║    1560 ║     -     ║     -      ║    -    ║    -    ║       -       ║    1    │  HIT   │  YES   │  0x00000000      ║
║    1580 ║     1     ║ 0x10000000 ║ READ    ║  1B     ║       -       ║    -    │   -    │    -    │        -         ║
║         ║           ║            ║ [UNCACHED ACCESS]                                                                  ║
║    1600 ║     -     ║     -      ║    -    ║    -    ║       -       ║    1    │  MISS  │  YES   │  0x000000ff      ║
╚═════════╩═══════════╩════════════╩═════════╩═════════╩═══════════════╩═════════╧════════╧═════════╧══════════════════╝
```

## Implementation notes

### Files

- **Logger**: `rtl/core/stage04_memory/cache_logger.sv`
- **Hookup**: instantiated from `rtl/core/stage04_memory/memory.sv`
- **Defines**: `LOG_CACHE` in `rtl/include/level_defines.svh`
- **Makefile**: root `makefile` Verilator section passes `LOG_CACHE` and related defines

### Signals

The logger taps the memory-stage cache interface:

```systemverilog
input dcache_req_t cache_req_i;  // Request toward cache
input dcache_res_t cache_res_i;  // Response from cache
```

### Performance

- Only active when `LOG_CACHE=1`
- When disabled, intended to optimize away in synthesis (no overhead)
- Small simulation-time cost when enabled

## Troubleshooting

### No log output

1. Confirm `LOG_CACHE=1` on the Verilator build and run.
2. Rebuild: `make verilate LOG_CACHE=1`
3. Ensure the workload actually exercises the cache path.

### Log volume too high

Cache logs are verbose. Filter at the shell:

```bash
make run:your_test LOG_CACHE=1 | grep "READ "
make run:your_test LOG_CACHE=1 | grep "WRITE"
make run:your_test LOG_CACHE=1 | grep "MISS"
```

## Related docs

- Memory stage: `rtl/core/stage04_memory/memory.sv`
- Cache RTL: `rtl/core/mmu/cache.sv`, `rtl/core/mmu/dcache.sv`, etc.
- Defines: `rtl/include/level_defines.svh`
