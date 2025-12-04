---
title: "RTL Modüler Mimarisi"
description: "Ceres RISC-V RTL tasarımının modüler yapısı ve archi"
date: 2025-12-01
draft: false
weight: 300
---

# Ceres RISC-V RTL Modüler Mimarisi

Bu bölüm Ceres RISC-V processor'ünün Register Transfer Level (RTL) tasarımını modüler olarak açıklamaktadır. Her modül kendi bölümünde detaylı bir şekilde incelenmiştir.

---

## 📋 RTL Yapısı (Dizin Yapısı)

```
rtl/
├── pkg/                          # Parametreler & type tanımları
│   └── ceres_param.sv
├── include/                      # Header dosyaları
│   └── *.svh
├── core/                         # CPU çekirdeği
│   ├── cpu.sv                    # Top-level CPU module
│   ├── hazard_unit.sv            # Pipeline hazard yönetimi
│   ├── stage01_fetch/            # Instruction Fetch aşaması
│   │   ├── fetch.sv
│   │   ├── align_buffer.sv
│   │   ├── compressed_decoder.sv
│   │   ├── gshare_bp.sv          # Gshare Branch Predictor
│   │   └── ras.sv                # Return Address Stack
│   ├── stage02_decode/           # Instruction Decode aşaması
│   │   ├── decode.sv
│   │   ├── control_unit.sv
│   │   ├── reg_file.sv           # 32x32-bit Register File
│   │   └── extend.sv             # Immediate extension
│   ├── stage03_execute/          # Execution aşaması
│   │   ├── execution.sv
│   │   ├── alu.sv                # Arithmetic Logic Unit
│   │   ├── cs_reg_file.sv        # CSR (Control & Status Registers)
│   │   └── mul_div/              # Multiply/Divide modülü
│   │       ├── mul_int.sv        # Integer multiplier
│   │       ├── divu_int.sv       # Unsigned divider
│   │       └── wallace32x32/     # Wallace tree multiplier
│   │           ├── mul.sv
│   │           ├── wallace.sv
│   │           ├── dadda.sv
│   │           ├── add.sv
│   │           ├── cla.sv        # Carry Look-Ahead
│   │           ├── ha.sv         # Half Adder
│   │           ├── fa.sv         # Full Adder
│   │           ├── configure.sv
│   │           └── mutex.sv
│   ├── stage04_memory/           # Memory aşaması
│   │   ├── memory.sv             # Load/Store işlemleri
│   │   ├── cache.sv              # L1 Data Cache
│   │   └── memory_arbiter.sv     # Memory arbitration
│   ├── stage05_writeback/        # Write-back aşaması
│   │   └── writeback.sv
│   ├── mmu/                      # Memory Management Unit
│   │   ├── cache.sv              # Cache controller
│   │   └── memory_arbiter.sv     # Memory arbiter
│   └── pmp_pma/                  # Physical Memory Protection
│       └── pma.sv                # Physical Memory Attributes
├── periph/                       # Peripherals (Çevre birimler)
│   ├── uart.sv                   # UART kontroller
│   ├── uart_rx.sv                # UART receiver
│   └── uart_tx.sv                # UART transmitter
├── ram/                          # Memory modülü
│   └── sp_bram.sv                # Single-port Block RAM
├── util/                         # Utility modülleri
│   └── fifo.sv                   # FIFO buffer
├── tracer/                       # Trace & Debug
│   └── konata_logger.sv          # Konata format tracer
└── wrapper/                      # Top-level wrappers
    ├── ceres_soc.sv              # SoC wrapper
    ├── ceres_wrapper.sv          # Main top module
    ├── ram_programmer.sv         # Memory programmer
    └── wrapper_ram.sv            # RAM interface wrapper
```

---

## 🎯 Modüller Hiyerarşisi

### Seviye 1: Top-Level (Top Module)

```
┌─────────────────────────────────────────────────────┐
│            ceres_wrapper.sv                         │
│  • System controller                                │
│  • Memory mapping                                   │
│  • Peripheral management                           │
└──────────────────┬──────────────────────────────────┘
                   │
        ┌──────────┴──────────┬──────────────────┐
        │                     │                  │
        ▼                     ▼                  ▼
┌───────────────┐  ┌──────────────────┐  ┌──────────────┐
│ ceres_soc.sv  │  │  periph/         │  │ wrapper_ram  │
│ (SoC core)    │  │  (UART, etc.)    │  │ (RAM iface)  │
└───────────────┘  └──────────────────┘  └──────────────┘
        │
        ▼
┌─────────────────────────────────────────────────────┐
│              cpu.sv                                 │
│  • CPU pipeline orchestration                       │
│  • Hazard detection & stall management              │
│  • Exception handling                               │
│  • Pipeline forwarding logic                        │
└──────────────┬────────────────────────────────────┘
               │
    ┌──────────┼──────────┬──────────┬──────────┐
    │          │          │          │          │
    ▼          ▼          ▼          ▼          ▼
┌──────┐  ┌──────┐  ┌──────┐  ┌──────┐  ┌──────┐
│Fetch │  │Decode│  │Exec  │  │Mem   │  │WB    │
│Stage1│  │Stage2│  │Stage3│  │Stage4│  │Stage5│
└──────┘  └──────┘  └──────┘  └──────┘  └──────┘
```

### Seviye 2: Pipeline Aşamaları

Ceres 5-stage pipeline'ı:

1. **Stage 1 (IF)**: Instruction Fetch
2. **Stage 2 (ID)**: Instruction Decode
3. **Stage 3 (EX)**: Execution
4. **Stage 4 (MEM)**: Memory Access
5. **Stage 5 (WB)**: Write-Back

---

## 📍 Modül Referans Haritası

| Modül | Dosya | Amaç | Bağlantılar |
|-------|-------|------|-------------|
| **Top-Level** | `ceres_wrapper.sv` | SoC wrapper | → CPU, Periph, RAM |
| **CPU** | `cpu.sv` | Pipeline orchestrator | → Tüm stages |
| **Hazard Unit** | `hazard_unit.sv` | Stall & forward logic | ← Tüm stages |
| **Fetch** | `fetch.sv` | Instruction fetch | → IF stage |
| **Decode** | `decode.sv` | Inst decoding | → ID stage |
| **Execute** | `execution.sv` | ALU, CSR | → EX stage |
| **Memory** | `memory.sv` | Load/Store | → MEM stage |
| **Write-Back** | `writeback.sv` | Register update | → WB stage |
| **ALU** | `alu.sv` | Arithmetic operations | ← Execute |
| **CSR File** | `cs_reg_file.sv` | Control registers | ← Execute |
| **Multiplier** | `mul_int.sv` | Integer MUL | ← Execute |
| **Divider** | `divu_int.sv` | Integer DIV | ← Execute |
| **Register File** | `reg_file.sv` | GP registers (x0-x31) | ← Decode |
| **Cache** | `cache.sv` | L1 I/D cache | ← Memory |
| **UART** | `uart.sv` | Serial I/O | ← Wrapper |
| **RAM** | `sp_bram.sv` | Memory | ← Memory arbiter |

---

## 🔄 Dataflow: Instruction Execution Path

```
┌─────────────────────────────────────────────────────────────┐
│               INSTRUCTION EXECUTION PATH                    │
└─────────────────────────────────────────────────────────────┘

1. FETCH (Instruction Memory)
   ├─ PC → I-Cache
   ├─ I-Cache → Align Buffer
   ├─ Align Buffer → Compressed Decoder (if C ext)
   ├─ Instruction → Output
   └─ Exception detection (DEBUG, MISALIGNED, ACCESS_FAULT, ILLEGAL)
                    │
                    ▼
2. DECODE (Instruction Decoding)
   ├─ Opcode → Control Unit
   ├─ Registers rs1, rs2 → Register File
   ├─ Immediate → Extender
   ├─ Forward logic check
   └─ Exception from ID stage
                    │
                    ▼
3. EXECUTE (ALU & Operations)
   ├─ Operands from RS1, RS2 (or forwarded)
   ├─ ALU → Arithmetic result
   ├─ CSR operations → CSR File
   ├─ MUL/DIV (if enabled)
   ├─ Branch target calculation
   └─ Exception from EX stage (LOAD_MISALIGNED, etc.)
                    │
                    ▼
4. MEMORY (Load/Store)
   ├─ Address calculation
   ├─ Cache lookup/access
   ├─ Load data extraction / Store
   └─ Exception (DATA_MISALIGNED, ACCESS_FAULT)
                    │
                    ▼
5. WRITE-BACK (Result Storage)
   ├─ Select source (ALU, Memory, CSR, PC+4)
   ├─ Write to destination register (rd)
   └─ Pipeline forwarding signals
```

---

## 🌊 Signal Flow Diyagramı

```
┌─────────────────────────────────────────────────────────┐
│  PIPELINE CONTROL SIGNALS                               │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  hazard_unit.sv                                         │
│  ├─ stall_i       → Pipeline stall cause               │
│  ├─ fwd_a, fwd_b  → Data forwarding multiplexer        │
│  ├─ flush_i       → Exception flush                    │
│  └─ flush_pc_i    → Exception handler PC                │
│                                                         │
│  cpu.sv (Orchestrator)                                 │
│  ├─ lx_ireq/res   → I-Cache interface                  │
│  ├─ lx_dreq/res   → D-Cache interface                  │
│  ├─ iomem_req/res → I/O memory interface               │
│  └─ trap signals  → Exception coordination              │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

---

## 📊 Modül Dependency Graph

```
┌──────────────────────────────────────────────────────────┐
│              MODÜLLER BAĞIMLILIK GRAFI                   │
├──────────────────────────────────────────────────────────┤

ceres_wrapper.sv
    ├──→ ceres_soc.sv
    │    └──→ cpu.sv
    │         ├──→ hazard_unit.sv
    │         ├──→ fetch.sv
    │         │    ├──→ align_buffer.sv
    │         │    ├──→ compressed_decoder.sv
    │         │    ├──→ gshare_bp.sv
    │         │    └──→ ras.sv
    │         ├──→ decode.sv
    │         │    ├──→ control_unit.sv
    │         │    ├──→ reg_file.sv
    │         │    └──→ extend.sv
    │         ├──→ execution.sv
    │         │    ├──→ alu.sv
    │         │    ├──→ cs_reg_file.sv
    │         │    └──→ mul_div/ (mul_int, divu_int, wallace32x32)
    │         ├──→ memory.sv
    │         │    └──→ cache.sv
    │         └──→ writeback.sv
    ├──→ periph/
    │    ├──→ uart.sv
    │    ├──→ uart_rx.sv
    │    └──→ uart_tx.sv
    ├──→ ram/
    │    └──→ sp_bram.sv
    └──→ wrapper_ram.sv

┌──────────────────────────────────────────────────────────┐
│              PACKAGE IMPORTS                             │
├──────────────────────────────────────────────────────────┤

Tüm modüller:
    ├─ import ceres_param::*;
    │  └─ Parametreler, typedef'ler, type tanımları
    └─ `include "ceres_defines.svh"
       └─ Makrolar ve define'lar

```

---

## 🎛️ Konfigürasyon Parametreleri

Tüm modüllerin temelinde `rtl/pkg/ceres_param.sv` dosyası yer almaktadır.

### Ana Parametreler

```systemverilog
// Sistem parametreleri
localparam CPU_CLK = 50_000_000;              // 50 MHz (varsayılan)
localparam PROG_BAUD_RATE = 115200;           // UART baud rate
localparam PROGRAM_SEQUENCE = "CERESTEST";    // Boot sequence
localparam RESET_VECTOR = 32'h8000_0000;      // Başlama adresi
localparam RAS_SIZE = 8;                       // Return Address Stack size
localparam XLEN = 32;                          // 32-bit (word length)
localparam BLK_SIZE = 128;                     # Cache line size (bits)

// Cache parametreleri
localparam IC_WAY = 8;                         // I-Cache: 8 ways
localparam DC_WAY = 8;                         // D-Cache: 8 ways
localparam IC_CAPACITY = 32 * (2 ** 10) * 8;  // I-Cache: 256 KB
localparam DC_CAPACITY = 32 * (2 ** 10) * 8;  // D-Cache: 256 KB

// Multiplier seçimi
localparam Mul_Type = 0;  // 0: Wallace tree, 1: Dadda multiplier
```

---

## 🔗 Bağlantı Noktaları (Interface)

Modüller arasında veri akışı şu ana arayüzler üzerinde gerçekleşir:

### CPU → Memory Interface
```systemverilog
ilowX_req_t  lx_ireq;   // Instruction request
ilowX_res_t  lx_ires;   // Instruction response
dlowX_req_t  lx_dreq;   // Data request
dlowX_res_t  lx_dres;   // Data response
```

### CPU → I/O Interface
```systemverilog
iomem_req_t  iomem_req; // I/O memory request
iomem_res_t  iomem_res; // I/O memory response
```

### Control Signals
```systemverilog
stall_e       stall_cause;  // Pipeline stall nedeni
logic         flush_i;      // Pipeline flush (exception)
logic [31:0]  flush_pc_i;   // Flush target PC
logic [31:0]  trap_pc;      // Exception handler PC
```

---

## ⚙️ Pipeline Senkronizasyonu

```
Clock Domains:
    All modules: clk_i (single clock domain)
    
Reset Sequence:
    1. rst_ni = 0 (active low)
    2. Tüm registers reset edilir
    3. PC ← RESET_VECTOR
    4. Pipeline flushed
    5. rst_ni = 1 (normal operation)

Stall Management:
    stall_cause ∈ {
        NO_STALL,
        LOAD_RAW_STALL,     // Load-Use data hazard
        IMISS_STALL,        // I-Cache miss
        DMISS_STALL,        // D-Cache miss
        ALU_STALL,          // ALU (MUL/DIV) latency
        FENCEI_STALL        // FENCE.I memory barrier
    }
```

---

## 📋 Modül Özet Tablosu

| Modül | Dosya Sayısı | Satır Sayı | Amaç | Latency |
|-------|--------------|-----------|------|---------|
| **Fetch Stage** | 5 | ~1000 | I-fetch & prediction | 1 |
| **Decode Stage** | 4 | ~500 | Decoding & register read | 1 |
| **Execute Stage** | 6 | ~800 | ALU, CSR, MUL/DIV | 1-34 |
| **Memory Stage** | 3 | ~600 | Load/Store & cache | 1-10 |
| **Write-Back Stage** | 1 | ~100 | Result write | 1 |
| **Hazard Unit** | 1 | ~300 | Stall & forward | Comb |
| **Multiplier** | 10 | ~1500 | 32x32 Wallace tree | 2 |
| **Divider** | 1 | ~400 | Integer divider | 34 |
| **ALU** | 1 | ~200 | Arithmetic logic | Comb |
| **Register File** | 1 | ~100 | 32x32 bit | 1 |
| **CSR File** | 1 | ~300 | Control registers | 1 |
| **Cache** | 1 | ~800 | L1 caches | 1-10 |
| **UART** | 3 | ~500 | Serial I/O | — |
| **RAM** | 1 | ~150 | Memory | — |
| **Tracer** | 1 | ~300 | Simulation trace | — |
| **Wrapper** | 4 | ~600 | Top-level | — |

---

## 🚀 Pipeline Execution Timeline

Instruction'un CPU içindeki yolculuğu:

```
Cycle 1 (IF):
    PC → Instruction Memory/Cache
    Fetch valid instruction & PC increment
    
Cycle 2 (ID):
    Instruction decode
    Register file read (rs1, rs2)
    Immediate extension
    
Cycle 3 (EX):
    ALU operation
    Branch target calculation
    CSR read/write
    
Cycle 4 (MEM):
    Memory address calculation
    Data cache access (load/store)
    
Cycle 5 (WB):
    Write result to destination register
    Signal next instruction
    
Hazard resolution:
    Data forwarding (EX→ID, MEM→ID, WB→ID)
    Stall on Load-Use RAW
    Stall on I-Cache miss
    Stall on D-Cache miss
    Stall on MUL/DIV latency
```

---

## 🎓 Sonraki Bölümler

Her modül için detaylı dökümantasyon:

- [Fetch Stage (Stage 1)](./stages/fetch_stage.md)
- [Decode Stage (Stage 2)](./stages/decode_stage.md)
- [Execute Stage (Stage 3)](./stages/execute_stage.md)
- [Memory Stage (Stage 4)](./stages/memory_stage.md)
- [Write-Back Stage (Stage 5)](./stages/writeback_stage.md)
- [Hazard Unit](./units/hazard_unit.md)
- [Peripheral: UART](./periph/uart.md)
- [Memory: BRAM](./memory/bram.md)

---

**Versiyon**: 1.0  
**Son Güncelleme**: 1 Aralık 2025

