# Cache logger — technical documentation

## Overview

`cache_logger` prints a **text table** of unified-cache requests and responses during simulation. It is intended for debug only and is compiled in when `LOG_CACHE` is defined.

## File location

```
rtl/core/stage04_memory/cache_logger.sv
```

## Ports

| Port | Description |
|------|-------------|
| `clk_i`, `rst_ni` | Clock and reset |
| `cache_req_i` | `dcache_req_t` — same view as the unified cache request |
| `cache_res_i` | `dcache_res_t` — cache response |

## Enabling

```bash
make verilate LOG_CACHE=1
# or your usual run target with LOG_CACHE=1
```

## Output

ASCII table with time, request fields (valid, address, R/W, size, write data, uncached), and response fields (valid, miss/hit, ready, read data). See also the in-repo note:

```
rtl/core/stage04_memory/CACHE_LOGGER_README.md
```

## Synthesis

Guarded by `` `ifdef LOG_CACHE `` (or equivalent define chain from the makefile). Should not affect ASIC when defines are off.

## Related

- [Memory stage](memory_module.md)
- [Cache (unified view)](../mmu/cache_module.md)
