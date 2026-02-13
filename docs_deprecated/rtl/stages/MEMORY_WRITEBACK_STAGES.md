---
title: "Memory & WriteBack Stages"
description: "Memory işlemleri (load/store), cache, writeback"
date: 2025-12-01
draft: false
weight: 340
---

# Memory & WriteBack Stages

Son iki pipeline aşaması: Memory (MEM - aşama 4) ve WriteBack (WB - aşama 5).

---

## 📋 Overview

| Aşama | Görev | Modül | Satır |
|-------|-------|-------|-------|
| **Memory (MEM)** | Load/Store, Cache, Peripherals | `memory.sv` | 170 |
| **WriteBack (WB)** | Register dosyasına yazma | `writeback.sv` | 50 |

---

## 💾 Memory Stage (MEM) - memory.sv

### Purpose

Memory aşaması:
- **Load Operations**: Data cache'den oku
- **Store Operations**: Data cache'ye yaz
- **Address Translation**: PMA (Physical Memory Attributes)
- **Peripheral Access**: UART, GPIO gibi cihazlar
- **Cache Stalling**: Cache miss'te pipeline'ı durdur

### Interface

```systemverilog
module memory
  import ceres_param::*;
(
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  stall_e                stall_i,
    
    // Data Cache Low Interface
    input  dlowX_res_t            lx_dres_i,      // Cache response
    output dlowX_req_t            lx_dreq_o,      // Cache request
    
    // Execute stage data request
    input  data_req_t             ex_data_req_i,  // From EX stage
    
    // Memory stage data request
    input  data_req_t             me_data_req_i,  // Current stage
    
    // Outputs
    output logic       [XLEN-1:0] me_data_o,      // Load data (to WB)
    output logic                  dmiss_stall_o,  // Data miss stall
    output logic                  fencei_stall_o, // Fence.i stall
    
    // UART
    output logic                  uart_tx_o,
    input  logic                  uart_rx_i,
    
    // Cache flush
    input  logic                  fe_flush_cache_i
);
```

### Data Request Structure

```systemverilog
typedef struct packed {
    logic        [XLEN-1:0] addr;      // Memory address
    logic        [XLEN-1:0] data;      // Store data
    logic                   rw;        // Read (0) or Write (1)
    logic        [     1:0] rw_size;   // Size: 01=byte, 10=half, 11=word
    logic                   ld_op_sign; // Sign-extend load?
    logic                   valid;     // Request valid
} data_req_t;
```

### Block Diagram

```
┌─────────────────────────────────────────────┐
│        Memory Stage (MEM)                   │
├─────────────────────────────────────────────┤
│                                             │
│  Execute Stage Request                      │
│  (ex_data_req_i)                            │
│         │                                    │
│         ▼                                    │
│  ┌──────────────────────────────────────┐  │
│  │  Memory Region Detection (PMA)       │  │
│  │  ├─ Address in cached region?        │  │
│  │  ├─ Address in peripheral region?    │  │
│  │  └─ Uncached access?                 │  │
│  └────────┬─────────────────────────────┘  │
│           │                                  │
│  ┌────────▼───────────┐    ┌────────────┐  │
│  │  Data Cache        │    │ Peripherals│  │
│  │  (L1-D)            │    │ (UART, etc)│  │
│  │  ├─ Load hit       │    │            │  │
│  │  ├─ Load miss      │    │ mem_mapped │  │
│  │  └─ Store         │    │ I/O        │  │
│  └────────┬───────────┘    └────────────┘  │
│           │                         │       │
│  ┌────────▼─────────────────────────▼────┐ │
│  │  Read Data Alignment & Sign-Extend    │ │
│  │  (byte/halfword/word selection)       │ │
│  └────────┬────────────────────────────────┤ │
│           │                                 │
│           ▼                                 │
│  ┌──────────────────────────────────────┐  │
│  │  To WriteBack Stage                  │  │
│  │  (me_data_o)                         │  │
│  └──────────────────────────────────────┘  │
│                                             │
└─────────────────────────────────────────────┘
```

### Memory Request Processing

```systemverilog
// Step 1: Edge detection - new request detection
logic ex_valid_q;
logic [XLEN-1:0] ex_addr_q, ex_rw_q, ex_rw_size_q;

always_ff @(posedge clk_i) begin
    ex_valid_q   <= ex_data_req_i.valid;
    ex_addr_q    <= ex_data_req_i.addr;
    ex_rw_q      <= ex_data_req_i.rw;
    ex_rw_size_q <= ex_data_req_i.rw_size;
end

// Step 2: Detect request change (new or address/data changed)
logic req_changed;
assign req_changed = (ex_data_req_i.addr != ex_addr_q) ||
                    (ex_data_req_i.rw != ex_rw_q) ||
                    (ex_data_req_i.rw_size != ex_rw_size_q) ||
                    (ex_data_req_i.valid && !ex_valid_q);

// Step 3: Start new transaction if region is cached and no active trans
assign mem_req_fire = ex_data_req_i.valid && req_changed && 
                     memregion && !mem_txn_active;

// Step 4: Track active transaction
logic mem_txn_active;
always_ff @(posedge clk_i) begin
    if (!rst_ni || fe_flush_cache_i) begin
        mem_txn_active <= 1'b0;
    end else begin
        if (dcache_res.valid) begin
            mem_txn_active <= 1'b0;  // Response received
        end
        if (mem_req_fire) begin
            mem_txn_active <= 1'b1;  // New request fired
        end
    end
end
```

### Address Decoding (PMA)

```systemverilog
// Physical Memory Attributes (PMA)
pma i_dpma (
    .addr_i      (ex_data_req_i.addr),
    .uncached_o  (uncached),      // Device (not cacheable)
    .memregion_o (memregion),     // Main memory?
    .grand_o     (grand)          // Granule
);

// memregion=1: Data Cache
// memregion=0: Peripheral Bus (UART, GPIO, etc.)
```

### Data Cache Access

```systemverilog
always_comb begin
    dcache_req.valid    = mem_req_fire;      // New request
    dcache_req.addr     = ex_data_req_i.addr;
    dcache_req.rw       = ex_data_req_i.rw;  // 0=read, 1=write
    dcache_req.rw_size  = ex_data_req_i.rw_size;
    dcache_req.data     = ex_data_req_i.data; // Write data
    dcache_req.uncached = uncached;
end

// Stall on cache miss
always_comb begin
    if (memregion) begin
        // Cache access: stall if new req or miss
        dmiss_stall_o = mem_req_fire || 
                       (mem_txn_active && !dcache_res.valid);
    end else begin
        // Peripheral: no stall
        dmiss_stall_o = 1'b0;
    end
end
```

### Load Data Alignment & Sign Extension

```systemverilog
always_comb begin : read_data_size_handler
    // Select source: cache or peripheral
    rd_data = !memregion ? pherip_rdata : dcache_res.data;
    me_data_o = '0;
    
    // Extract byte/halfword based on address alignment
    selected_byte = rd_data[(ex_data_req_i.addr[1:0]*8)+:8];
    selected_halfword = rd_data[(ex_data_req_i.addr[1]*16)+:16];
    
    // Size + Sign extend
    unique case (ex_data_req_i.rw_size)
        2'b01: begin  // Byte
            me_data_o = ex_data_req_i.ld_op_sign ? 
                       {{24{selected_byte[7]}}, selected_byte} :      // LB (signed)
                       {24'b0, selected_byte};                        // LBU (unsigned)
        end
        2'b10: begin  // Halfword
            me_data_o = ex_data_req_i.ld_op_sign ?
                       {{16{selected_halfword[15]}}, selected_halfword} :  // LH
                       {16'b0, selected_halfword};                          // LHU
        end
        2'b11: begin  // Word
            me_data_o = rd_data;  // LW (full word)
        end
        default: me_data_o = '0;
    endcase
end
```

### Load Examples

```
Example 1: LB x3, 1(x5)  ; Load byte from x5+1, sign-extend
├─ addr = x5 + 1, rw_size = 2'b01 (byte), ld_op_sign = 1
├─ Memory contains: 0xAABBCCDD at address x5
├─ Byte at offset 1: 0xCC (bits[15:8])
├─ selected_byte = 0xCC
├─ Sign extension: if 0xCC[7]=1 → {{24{1}}, 0xCC} = 0xFFFFFFCC
└─ me_data_o = 0xFFFFFFCC

Example 2: LBU x3, 1(x5)  ; Load byte, zero-extend
├─ Same address, but ld_op_sign = 0
├─ selected_byte = 0xCC
├─ Zero extension: {{24{0}}, 0xCC} = 0x000000CC
└─ me_data_o = 0x000000CC

Example 3: LH x3, 2(x5)  ; Load halfword
├─ addr = x5 + 2, rw_size = 2'b10 (halfword)
├─ Memory: 0xAABBCCDD
├─ Halfword at offset 2: 0xCCDD (bits[31:16])
├─ selected_halfword = 0xCCDD
├─ If ld_op_sign=1: {{16{1}}, 0xCCDD} = 0xFFFFCCDD
└─ me_data_o = 0xFFFFCCDD
```

### Peripheral Access (UART)

```systemverilog
always_comb begin
    // When NOT in memory region (memregion=0)
    pherip_valid = !memregion && !fe_flush_cache_i && 
                  !(stall_i inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL});
    pherip_addr  = !memregion ? ex_data_req_i.addr : '0;
    pherip_sel   = pherip_valid ? 4'b1111 : 4'b0000;
    pherip_wdata = !memregion ? ex_data_req_i.data : '0;
end

// Connect to UART
uart i_uart (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .stb_i      (pherip_valid),          // Strobe
    .adr_i      (pherip_addr[3:2]),      // Address (word-aligned)
    .byte_sel_i (pherip_sel),            // Byte select
    .we_i       (ex_data_req_i.rw),      // Write enable
    .dat_i      (pherip_wdata),          // Write data
    .dat_o      (pherip_rdata),          // Read data
    .uart_rx_i  (uart_rx_i),
    .uart_tx_o  (uart_tx_o)
);
```

---

## 🖊️ WriteBack Stage (WB) - writeback.sv

### Purpose

WriteBack aşaması:
- **Register Write**: Register dosyasına sonuç yaz
- **Result Selection**: ALU result / Memory data / PC+4
- **Stall Filtering**: Stall'dan sonra yazma gereksiz

### Interface

```systemverilog
module writeback
  import ceres_param::*;
(
    input  logic                       clk_i,
    input  logic                       rst_ni,
    input  stall_e                     stall_i,
    
    // Result sources
    input  logic        [     1:0] data_sel_i,      // Result selector
    input  logic        [XLEN-1:0] alu_result_i,   // ALU result
    input  logic        [XLEN-1:0] read_data_i,    // Memory load data
    input  logic        [XLEN-1:0] pc_i,           // PC
    input  logic        [XLEN-1:0] pc_incr_i,      // PC+4
    
    // Register file write
    input  logic                    rf_rw_en_i,    // Write enable
    input  logic        [     4:0] rd_addr_i,      // Destination register
    output logic                    rf_rw_en_o,    // Filtered write enable
    output logic        [XLEN-1:0] wb_data_o,      // Write data to register
    
    // Cache & Stall control
    input  logic                    fe_flush_cache_i
);
```

### Result Selection (data_sel)

```systemverilog
// Result source multiplexer
always_comb begin
    // data_sel_i[1:0]:
    //   2'b00 → ALU result
    //   2'b01 → Memory data (load)
    //   2'b10 → PC+4 (jump link)
    //   2'b11 → (reserved)
    
    if (data_sel_i[1]) begin
        wb_data_o = pc_incr_i;         // 2'b1x → PC+4 (JAL, JALR)
    end else if (data_sel_i[0]) begin
        wb_data_o = read_data_i;       // 2'b01 → Memory data (Load)
    end else begin
        wb_data_o = alu_result_i;      // 2'b00 → ALU result (default)
    end
end
```

### Stall Filtering

```systemverilog
// Only write register if:
// 1. rf_rw_en_i is asserted (instruction writes register)
// 2. NOT flushing cache
// 3. NOT stalling (certain stall types cancel write)

always_comb begin
    if (rf_rw_en_i && !fe_flush_cache_i && 
        !(stall_i inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL})) begin
        rf_rw_en_o = 1'b1;
    end else begin
        rf_rw_en_o = 1'b0;  // Don't write
    end
end
```

### Result Source Examples

```
Example 1: ADD x3, x1, x2
├─ data_sel_i = 2'b00 (ALU result)
├─ alu_result_i = (x1 + x2)
├─ wb_data_o = alu_result_i
└─ x3 ← wb_data_o

Example 2: LW x5, 0(x6)
├─ data_sel_i = 2'b01 (Memory data)
├─ read_data_i = (value from memory)
├─ wb_data_o = read_data_i
└─ x5 ← wb_data_o

Example 3: JAL x1, 100
├─ data_sel_i = 2'b10 (PC+4)
├─ pc_incr_i = PC + 4 (return address)
├─ wb_data_o = pc_incr_i
└─ x1 ← wb_data_o (return address saved)

Example 4: SW x5, 0(x6)
├─ rf_rw_en_i = 0 (no register write)
├─ wb_data_o = (don't care)
└─ Store instruction, no register update
```

---

## 📊 Full Pipeline Example

### Scenario: Load from Memory → Use in Next ADD

```
Cycle  Fetch     Decode       Execute      Memory       WriteBack
─────────────────────────────────────────────────────────────────
  0     IF₁       -             -            -            -
  1     IF₂       ID₁(LW)       -            -            -
  2     IF₃       ID₂(ADD)      EX₁(LW)      -            -
  3     IF₄       ID₃(SW)       EX₂(ADD)     MEM₁(LW)     -
  4     -         -             EX₃(SW)      MEM₂(ADD)    WB₁(LW)
                                                          ├─ Load data
                                                          └─ x3 ← load_data

  5     -         -             -            MEM₃(SW)     WB₂(ADD)
                                                          ├─ ADD result
                                                          └─ x8 ← add_result
```

### Timing with Cache Miss

```
Cycle  Execute  Memory        Write Back
─────────────────────────────────────────
  0     EX       MEM           WB
       (LW req)

  1     STALL    DMISS_STALL   DMISS_STALL
       (stall)  (cache miss)

  2     STALL    DMISS_STALL   DMISS_STALL
       (stall)  (waiting...)

  3     STALL    DMISS_STALL   DMISS_STALL
       (stall)  (cache miss)

  4     STALL    MEM           DMISS_STALL
       (stall)  (hit response)

  5     -        -             WB
                              (data to register)
```

---

## 🔄 Load-Use Hazard & Forwarding

### Problem

```
LW x3, 0(x5)     ; Cycle 0-3: Load from memory
ADD x7, x3, x4   ; Cycle 1-4: Decode, starts reading x3

Timeline:
├─ Cycle 2: ADD in EX stage needs x3 value (not yet in register!)
├─ x3 written to register in Cycle 4 (WB stage)
└─ Hazard: ADD reads old/uninitialized x3
```

### Solution: Data Forwarding

Forwarding unit provides:
- **Fwd_a[1:0]**: Source for operand A (register / WB data / ALU result)
- **Fwd_b[1:0]**: Source for operand B

```
ADD (EX stage, Cycle 2):
├─ x3 not ready yet
├─ Forwarding detects: x3 destination = LW output
├─ Fwd_a = 2'b10 (from previous ALU)
└─ Operand A ← forwarded value (or from WB when available)
```

---

## 📈 Memory Map for Peripherals

```
0x2000_0000 ┌─────────────────────┐
            │  UART (4 regs)      │
0x2000_000F ├─────────────────────┤
            │  GPIO (8 regs)      │
0x2000_001F ├─────────────────────┤
            │  SPI (16 regs)      │
0x2000_003F ├─────────────────────┤
            │  I2C (8 regs)       │
0x2000_004F ├─────────────────────┤
            │  PWM (16 regs)      │
0x2000_005F ├─────────────────────┤
            │  Timer (8 regs)     │
0x2000_006F ├─────────────────────┤
            │  PLIC (4K)          │
0x2000_0FFF └─────────────────────┘
```

### UART Register Map

```
Offset  Name        R/W  Purpose
──────────────────────────────────────
 0x00   TX_DATA     W    Transmit data
 0x04   RX_DATA     R    Receive data
 0x08   CONTROL     RW   Baud rate, enable
 0x0C   STATUS      R    TX/RX busy flags
```

---

## 🎯 Summary

### Memory Stage
- **Load/Store handling** from data cache or peripherals
- **Address decoding** (memory vs. I/O)
- **Data alignment** and sign extension
- **Cache stalling** on miss

### WriteBack Stage
- **Result selection** (ALU / Memory / PC+4)
- **Register write filtering** (respect stalls)
- **Data forwarding** path to Execute stage

| Aspect | Memory | WriteBack |
|--------|--------|-----------|
| **Latency** | 1-N cycles (cache miss) | 0 cycles (combinational) |
| **Load access** | Cache/Peripheral | - |
| **Store access** | Cache/Peripheral | - |
| **Register update** | - | Yes |
| **Forwarding source** | Read data | Write-back data |

---

## 📚 İlişkili Belgeler

- [Execute Stage](./EXECUTE_STAGE.md) - Önceki aşama
- [Fetch Stage](./FETCH_STAGE.md) - Pipeline başlangıcı
- [Data Cache](./cache.md) - L1-D cache detayları
- [UART Peripheral](../periph/uart.md) - UART modülü

---

**Versiyon**: 1.0  
**Son Güncelleme**: 1 Aralık 2025

