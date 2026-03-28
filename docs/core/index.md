# Level RISC-V Core

This section covers all modules of the Level RISC-V processor core.

## Hierarchy

```
rtl/core/
├── cpu.sv                    # Top-level CPU
├── hazard_unit.sv            # Pipeline hazard handling
├── stage01_fetch/            # Instruction Fetch
├── stage02_decode/           # Instruction Decode
├── stage03_execute/          # Execute (ALU, MUL/DIV)
├── stage04_memory/           # Memory Access
├── stage05_writeback/        # Write-back
├── mmu/                      # Memory Management
└── pmp_pma/                  # Physical Memory Protection
```

## Modules

### Top-Level

| Module | Description |
|--------|-------------|
| [CPU](cpu_module.md) | Top-level CPU module |
| [Hazard Unit](hazard_unit_module.md) | Pipeline hazard detection and forwarding |

### Pipeline Stages

| Stage | Modules |
|-------|---------|
| [Fetch](stage01_fetch/fetch_module.md) | Instruction fetch, branch prediction, RAS |
| Fetch (prefetch) + microarch notes | [Next-line prefetcher](stage01_fetch/next_line_prefetcher_module.md), [Prefetcher wrapper](stage01_fetch/prefetcher_wrapper_module.md), [Microarch ideas — fetch & memory](stage01_fetch/fetch-prefetch-future-ideas.md) |
| [Decode](stage02_decode/decode_module.md) | Instruction decode, register file |
| [Execute](stage03_execute/execution_module.md) | ALU, multiplier, divider, CSR |
| Execute (MUL/DIV variants) | [mul_int](stage03_execute/mul_int_module.md), [mul_pipelined](stage03_execute/mul_pipelined_module.md), [Wallace tree](stage03_execute/wallace_multiplier_module.md), [divu_int](stage03_execute/divu_int_module.md), [divu_pipelined](stage03_execute/divu_pipelined_module.md) |
| [Memory](stage04_memory/memory_module.md) | Load/store operations |
| Memory (helpers) | [Store buffer](stage04_memory/store_buffer_module.md), [Cache logger](stage04_memory/cache_logger_module.md) |
| [Writeback](stage05_writeback/writeback_module.md) | Register write-back |

### Memory System

| Module | Description |
|--------|-------------|
| [Cache (unified)](mmu/cache_module.md) | Top-level unified cache documentation |
| [I-cache](mmu/icache_module.md) | Standalone instruction cache |
| [D-cache](mmu/dcache_module.md) | Standalone data cache |
| [FENCE.I helper](mmu/dcache_fencei_module.md) | `dcache_fencei` write-back FSM |
| [L2 cache](mmu/l2_cache_module.md) | Non-blocking multi-bank L2 (`nbmbmp_l2_cache`) |
| [Memory Arbiter](mmu/memory_arbiter_module.md) | Instruction/Data arbiter |
| [WB Interconnect](mmu/wb_interconnect_module.md) | Wishbone interconnect |
| [PMA](pmp_pma/pma_module.md) | Physical Memory Attributes |

## Pipeline Diagram

```
┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐
│  FETCH  │──▶│ DECODE  │──▶│ EXECUTE │──▶│ MEMORY  │──▶│WRITEBACK│
└─────────┘   └─────────┘   └─────────┘   └─────────┘   └─────────┘
     │             │             │             │             │
     ▼             ▼             ▼             ▼             ▼
  Branch       Register       ALU/MUL       Load/       Register
  Predict      File Read      DIV/CSR       Store       Write
```
