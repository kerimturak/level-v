# CERES RISC-V Core

Bu bölüm, CERES RISC-V işlemci çekirdeğinin tüm modüllerini kapsar.

## Hiyerarşi

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

## Modüller

### Top-Level

| Modül | Açıklama |
|-------|----------|
| [CPU](cpu_module.md) | Top-level CPU modülü |
| [Hazard Unit](hazard_unit_module.md) | Pipeline hazard detection ve forwarding |

### Pipeline Stages

| Stage | Modüller |
|-------|----------|
| [Fetch](stage01_fetch/fetch_module.md) | Instruction fetch, branch prediction, RAS |
| [Decode](stage02_decode/decode_module.md) | Instruction decode, register file |
| [Execute](stage03_execute/execution_module.md) | ALU, multiplier, divider, CSR |
| [Memory](stage04_memory/memory_module.md) | Load/store operations |
| [Writeback](stage05_writeback/writeback_module.md) | Register write-back |

### Memory System

| Modül | Açıklama |
|-------|----------|
| [Cache](mmu/cache_module.md) | I-Cache ve D-Cache |
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
