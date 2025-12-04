# CERES Defines - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Feature Flags](#feature-flags)
3. [Multiplier Implementasyonları](#multiplier-implementasyonları)
4. [Trace ve Log Kontrolleri](#trace-ve-log-kontrolleri)
5. [Simülasyon Kontrolleri](#simülasyon-kontrolleri)
6. [Makefile Entegrasyonu](#makefile-entegrasyonu)
7. [Kullanım Örnekleri](#kullanım-örnekleri)

---

## Genel Bakış

### Amaç

`ceres_defines.svh` dosyası, CERES RISC-V işlemcisinin **compile-time konfigürasyonunu** sağlar. Bu header file, feature flag'ler, multiplier seçimi ve trace kontrolleri için merkezi tanımlar içerir.

### Dosya Konumu

```
rtl/include/ceres_defines.svh
```

### Include Yöntemi

```systemverilog
`include "ceres_defines.svh"
```

---

## Feature Flags

### Multiplier Seçimi

Tek seferde sadece bir multiplier implementasyonu aktif olmalıdır:

```systemverilog
//------------------------------------------------------------------------------
// MULTIPLIER IMPLEMENTATION SELECTION
// Enable only ONE of the following multiplier implementations
//------------------------------------------------------------------------------

// Single-cycle Wallace tree multiplier (default - best performance)
`define FEAT_WALLACE_SINGLE

// Multi-cycle Wallace tree multiplier (area optimized)
//`define FEAT_WALLACE_MULTI

// DSP block multiplier (FPGA optimized)
//`define FEAT_DSP_MUL
```

### Multiplier Karşılaştırma

| Implementasyon | Latency | Throughput | Area | Kullanım |
|----------------|---------|------------|------|----------|
| WALLACE_SINGLE | 1 cycle | 1/cycle | Yüksek | Performans |
| WALLACE_MULTI | N cycle | 1/N cycle | Düşük | Alan opt. |
| DSP_MUL | 1-3 cycle | 1/cycle | DSP | FPGA |

---

## Multiplier Implementasyonları

### Wallace Single (Varsayılan)

```systemverilog
`define FEAT_WALLACE_SINGLE

// Kullanım
`ifdef FEAT_WALLACE_SINGLE
    // Single-cycle 32x32 Wallace tree
    wallace_mul_single u_mul (
        .i_a    (operand_a),
        .i_b    (operand_b),
        .o_prod (product)
    );
`endif
```

**Özellikler:**
- Tek cycle'da 32x32 çarpma
- 64-bit sonuç
- Yüksek alan tüketimi
- Kritik yol uzunluğu

### Wallace Multi

```systemverilog
//`define FEAT_WALLACE_MULTI

// Kullanım
`ifdef FEAT_WALLACE_MULTI
    // Multi-cycle radix-4 Booth multiplier
    wallace_mul_multi u_mul (
        .clk_i      (clk),
        .rst_ni     (rst_n),
        .i_start    (mul_start),
        .i_a        (operand_a),
        .i_b        (operand_b),
        .o_prod     (product),
        .o_done     (mul_done)
    );
`endif
```

**Özellikler:**
- Multi-cycle çarpma (4-16 cycle)
- Düşük alan tüketimi
- Pipeline stall gerektirir

### DSP Multiplier

```systemverilog
//`define FEAT_DSP_MUL

// Kullanım
`ifdef FEAT_DSP_MUL
    // FPGA DSP48 block multiplier
    dsp_mul u_mul (
        .clk_i  (clk),
        .i_a    (operand_a),
        .i_b    (operand_b),
        .o_prod (product)
    );
`endif
```

**Özellikler:**
- FPGA DSP bloğu kullanır
- 1-3 cycle latency (pipeline)
- Düşük logic tüketimi
- Vendor spesifik

---

## Trace ve Log Kontrolleri

### Trace Flag'leri

Bu flag'ler normalde **comment halinde** tutulur ve **makefile üzerinden** aktive edilir:

```systemverilog
//------------------------------------------------------------------------------
// TRACE AND LOGGING CONTROLS
// These are typically enabled via makefile +define+ flags
//------------------------------------------------------------------------------

// `define COMMIT_TRACER     // Carry trace info in pipeline registers
// `define KONATA_TRACER     // Konata pipeline visualizer support
// `define LOG_COMMIT        // Spike-compatible commit trace
// `define LOG_RAM           // RAM initialization messages
// `define LOG_UART          // UART TX file logging
// `define LOG_BP            // Branch predictor statistics
// `define LOG_BP_VERBOSE    // Per-branch verbose logging
```

### Flag Açıklamaları

| Flag | Açıklama | Çıktı |
|------|----------|-------|
| `COMMIT_TRACER` | Pipeline register'larda trace bilgisi taşır | - |
| `KONATA_TRACER` | Konata pipeline visualizer desteği | `pipeline.log` |
| `LOG_COMMIT` | Spike ile karşılaştırılabilir commit trace | `commit.log` |
| `LOG_RAM` | RAM yükleme mesajları | Konsol |
| `LOG_UART` | UART TX çıktısı dosyaya log | `uart.log` |
| `LOG_BP` | Branch predictor istatistikleri | Konsol |
| `LOG_BP_VERBOSE` | Her branch için detaylı log | Konsol |

---

## Simülasyon Kontrolleri

### Simülasyon Flag'leri

```systemverilog
//------------------------------------------------------------------------------
// SIMULATION CONTROLS
// Enabled via makefile for simulation modes
//------------------------------------------------------------------------------

// `define SIM_FAST           // Disable all logging for speed
// `define SIM_UART_MONITOR   // UART monitoring + auto-stop
// `define SIM_COVERAGE       // Enable coverage collection
```

### SIM_FAST Modu

```systemverilog
`ifdef SIM_FAST
    // Tüm log'lar devre dışı
    // Maksimum simülasyon hızı
`else
    // Normal debug modunda
    `ifdef LOG_COMMIT
        // Commit trace aktif
    `endif
`endif
```

### SIM_UART_MONITOR

```systemverilog
`ifdef SIM_UART_MONITOR
    // UART çıktısını izle
    // "PASS" veya "FAIL" görünce simülasyonu durdur
    // Benchmark sonuçlarını algıla
`endif
```

---

## Makefile Entegrasyonu

### Verilator Flag Geçişi

```makefile
# Trace kontrolleri
LOG_COMMIT ?= 0
LOG_PIPELINE ?= 0
LOG_RAM ?= 0
LOG_UART ?= 0
LOG_BP ?= 0
LOG_BP_VERBOSE ?= 0
KONATA_TRACER ?= 0

# Verilator'a define geçir
VFLAGS_DEFINES :=
ifeq ($(LOG_COMMIT),1)
    VFLAGS_DEFINES += +define+LOG_COMMIT
endif
ifeq ($(KONATA_TRACER),1)
    VFLAGS_DEFINES += +define+KONATA_TRACER +define+COMMIT_TRACER
endif
# ... diğer flag'ler
```

### Kullanım Örnekleri

```bash
# Sadece commit trace
make run T=rv32ui-p-add LOG_COMMIT=1

# Pipeline visualizer
make run T=rv32ui-p-add KONATA_TRACER=1 LOG_PIPELINE=1

# Branch predictor stats
make cm LOG_BP=1 SIM_UART_MONITOR=1

# Hızlı simülasyon
make run T=coremark SIM_FAST=1

# Tüm log'lar
make run T=test LOG_COMMIT=1 LOG_RAM=1 LOG_UART=1 LOG_BP=1
```

---

## Kullanım Örnekleri

### Conditional Compilation

```systemverilog
module example
  import ceres_param::*;
(
    input logic clk_i,
    // ...
);

`ifdef FEAT_WALLACE_SINGLE
    // Single-cycle multiplier
    assign mul_done = 1'b1;  // Always ready
`elsif FEAT_WALLACE_MULTI
    // Multi-cycle multiplier
    logic mul_busy;
    // ...
`endif

`ifdef LOG_COMMIT
    always_ff @(posedge clk_i) begin
        if (commit_valid) begin
            $display("core   0: 0x%08x (0x%08x) x%0d 0x%08x",
                     commit_pc, commit_instr, commit_rd, commit_data);
        end
    end
`endif

endmodule
```

### Guard Pattern

```systemverilog
`ifndef CERES_DEFINES_SVH
`define CERES_DEFINES_SVH

// Define içerikleri

`endif // CERES_DEFINES_SVH
```

### Cross-Module Dependency

```systemverilog
// KONATA_TRACER aktifse, COMMIT_TRACER da gerekli
`ifdef KONATA_TRACER
    `ifndef COMMIT_TRACER
        `define COMMIT_TRACER
    `endif
`endif
```

---

## Flag Bağımlılıkları

### İlişki Diyagramı

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                          FLAG DEPENDENCIES                                       │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   KONATA_TRACER ──────────────────────► COMMIT_TRACER                           │
│        │                                     │                                   │
│        │                                     ▼                                   │
│        │                              Pipeline registers                         │
│        │                              carry trace info                           │
│        │                                                                         │
│        ▼                                                                         │
│   LOG_PIPELINE ─────────────────────► pipeline.log output                       │
│                                                                                  │
│                                                                                  │
│   LOG_COMMIT ───────────────────────► commit.log output                         │
│        │                                     │                                   │
│        │                                     ▼                                   │
│        │                              Spike comparison                           │
│        │                                                                         │
│                                                                                  │
│   SIM_FAST ─────────────────────────► Disables all LOG_*                        │
│                                                                                  │
│                                                                                  │
│   LOG_BP_VERBOSE ───────────────────► LOG_BP                                    │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### Implicit Dependencies

| Flag | Requires |
|------|----------|
| `KONATA_TRACER` | `COMMIT_TRACER` (auto-enabled) |
| `LOG_BP_VERBOSE` | `LOG_BP` (implied) |
| `SIM_FAST` | Disables all `LOG_*` flags |

---

## Best Practices

### 1. Multiplier Seçimi

```systemverilog
// Sadece bir multiplier aktif olmalı
`define FEAT_WALLACE_SINGLE
//`define FEAT_WALLACE_MULTI  // Comment out
//`define FEAT_DSP_MUL        // Comment out
```

### 2. Trace Log'ları

```systemverilog
// Normalde comment halinde
// Makefile ile aktive et
//`define LOG_COMMIT

// Makefile:
// make run T=test LOG_COMMIT=1
```

### 3. Debug vs Release

```bash
# Debug build (default)
make run T=test MODE=debug

# Release build (minimal logging)
make run T=coremark MODE=release SIM_FAST=1

# Test mode (assertions enabled)
make isa MODE=test
```

---

## Özet

`ceres_defines.svh` dosyası:

1. **Feature Selection**: Multiplier implementasyonu
2. **Trace Control**: Commit, pipeline, UART logging
3. **Simulation Modes**: Fast, coverage, UART monitor
4. **Makefile Integration**: Runtime flag geçişi
5. **Conditional Compilation**: `ifdef/endif` pattern

Bu header file, CERES RISC-V işlemcisinin farklı konfigürasyonlarını destekler.
# Exception Priority - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [RISC-V Exception Modeli](#risc-v-exception-modeli)
3. [Priority Konfigürasyonu](#priority-konfigürasyonu)
4. [Exception Türleri](#exception-türleri)
5. [Trap Handling](#trap-handling)
6. [Pipeline Entegrasyonu](#pipeline-entegrasyonu)
7. [Kullanım Örnekleri](#kullanım-örnekleri)

---

## Genel Bakış

### Amaç

`exception_priority.svh` dosyası, RISC-V exception'larının **öncelik sırasını** tanımlar. Aynı cycle'da birden fazla exception oluştuğunda hangi exception'ın işleneceğini belirler.

### Dosya Konumu

```
rtl/include/exception_priority.svh
```

### Temel Konsept

```
Aynı anda birden fazla exception oluşabilir:
- Instruction page fault (fetch)
- Illegal instruction (decode)
- Load/Store fault (memory)

Priority sayısı düşük olan exception önce işlenir.
```

---

## RISC-V Exception Modeli

### Exception vs Interrupt

| Tip | Özellik | Örnek |
|-----|---------|-------|
| **Exception** | Senkron, instruction kaynaklı | Illegal instruction |
| **Interrupt** | Asenkron, dış kaynaklı | Timer interrupt |

### Exception Sınıfları

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                         EXCEPTION CLASSIFICATION                                 │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                          INSTRUCTION EXCEPTIONS                          │   │
│   │                                                                          │   │
│   │   • Instruction Address Misaligned                                       │   │
│   │   • Instruction Access Fault                                             │   │
│   │   • Illegal Instruction                                                  │   │
│   │   • Breakpoint                                                           │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                            LOAD EXCEPTIONS                               │   │
│   │                                                                          │   │
│   │   • Load Address Misaligned                                              │   │
│   │   • Load Access Fault                                                    │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                           STORE EXCEPTIONS                               │   │
│   │                                                                          │   │
│   │   • Store/AMO Address Misaligned                                         │   │
│   │   • Store/AMO Access Fault                                               │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
│   ┌─────────────────────────────────────────────────────────────────────────┐   │
│   │                         ENVIRONMENT CALLS                                │   │
│   │                                                                          │   │
│   │   • Environment Call from U-mode                                         │   │
│   │   • Environment Call from S-mode                                         │   │
│   │   • Environment Call from M-mode                                         │   │
│   │                                                                          │   │
│   └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Priority Konfigürasyonu

### RISC-V Standart Priority

RISC-V spesifikasyonu exception önceliklerini belirler:

```systemverilog
// exception_priority.svh

`ifndef EXCEPTION_PRIORITY_SVH
`define EXCEPTION_PRIORITY_SVH

//------------------------------------------------------------------------------
// EXCEPTION PRIORITY CONFIGURATION
// Lower number = Higher priority
// Based on RISC-V Privileged Specification
//------------------------------------------------------------------------------

// Instruction Exceptions (highest priority for same instruction)
localparam int PRIORITY_INSTR_ADDR_MISALIGNED = 0;
localparam int PRIORITY_INSTR_ACCESS_FAULT    = 1;
localparam int PRIORITY_ILLEGAL_INSTR         = 2;
localparam int PRIORITY_BREAKPOINT            = 3;

// Load Exceptions
localparam int PRIORITY_LOAD_ADDR_MISALIGNED  = 4;
localparam int PRIORITY_LOAD_ACCESS_FAULT     = 5;

// Store Exceptions
localparam int PRIORITY_STORE_ADDR_MISALIGNED = 6;
localparam int PRIORITY_STORE_ACCESS_FAULT    = 7;

// Environment Calls (lowest priority)
localparam int PRIORITY_ECALL_U               = 8;
localparam int PRIORITY_ECALL_S               = 9;
localparam int PRIORITY_ECALL_M               = 10;

`endif // EXCEPTION_PRIORITY_SVH
```

### Priority Tablosu

| Priority | Exception | Code | Açıklama |
|----------|-----------|------|----------|
| 0 | Instruction Address Misaligned | 0 | En yüksek öncelik |
| 1 | Instruction Access Fault | 1 | I-Cache/Bus fault |
| 2 | Illegal Instruction | 2 | Geçersiz opcode |
| 3 | Breakpoint | 3 | EBREAK instruction |
| 4 | Load Address Misaligned | 4 | Unaligned load |
| 5 | Load Access Fault | 5 | D-Cache/Bus fault |
| 6 | Store Address Misaligned | 6 | Unaligned store |
| 7 | Store Access Fault | 7 | D-Cache/Bus fault |
| 8 | Environment Call U-mode | 8 | ECALL from User |
| 9 | Environment Call S-mode | 9 | ECALL from Supervisor |
| 10 | Environment Call M-mode | 11 | ECALL from Machine |

---

## Exception Türleri

### Instruction Address Misaligned

```systemverilog
// Fetch stage'de kontrol
// Compressed (RV32C) ile 2-byte aligned olabilir
// Standard instructions 4-byte aligned olmalı

logic instr_addr_misaligned;

`ifdef RV32C_ENABLED
    assign instr_addr_misaligned = pc[0];  // Bit 0 must be 0
`else
    assign instr_addr_misaligned = |pc[1:0];  // Bits 1:0 must be 0
`endif
```

### Instruction Access Fault

```systemverilog
// I-Cache miss + bus error
// PMA non-executable region
// PMP execute violation

logic instr_access_fault;

assign instr_access_fault = icache_error || 
                            pma_exec_fault || 
                            pmp_exec_fault;
```

### Illegal Instruction

```systemverilog
// Decode stage'de kontrol
// - Invalid opcode
// - Invalid funct3/funct7
// - CSR access violation

logic illegal_instr;

assign illegal_instr = !valid_opcode || 
                       invalid_funct || 
                       csr_access_fault;
```

### Load/Store Misaligned

```systemverilog
// Memory stage'de kontrol
// LW/SW: 4-byte aligned
// LH/SH: 2-byte aligned
// LB/SB: no alignment requirement

logic addr_misaligned;

always_comb begin
    case (mem_size)
        MEM_SIZE_WORD: addr_misaligned = |addr[1:0];
        MEM_SIZE_HALF: addr_misaligned = addr[0];
        MEM_SIZE_BYTE: addr_misaligned = 1'b0;
        default:       addr_misaligned = 1'b1;
    endcase
end
```

### Load/Store Access Fault

```systemverilog
// D-Cache miss + bus error
// PMA read/write violation
// PMP read/write violation

logic load_access_fault;
logic store_access_fault;

assign load_access_fault  = dcache_error && is_load;
assign store_access_fault = dcache_error && is_store;
```

---

## Trap Handling

### Exception Priority Resolver

```systemverilog
// Aynı cycle'da birden fazla exception varsa
// En yüksek öncelikli olanı seç

function automatic logic [3:0] resolve_exception_priority(
    input logic instr_addr_mis,
    input logic instr_access,
    input logic illegal,
    input logic breakpoint,
    input logic load_mis,
    input logic load_access,
    input logic store_mis,
    input logic store_access,
    input logic ecall
);
    // Priority order (low number = high priority)
    if (instr_addr_mis) return 4'd0;  // Instruction address misaligned
    if (instr_access)   return 4'd1;  // Instruction access fault
    if (illegal)        return 4'd2;  // Illegal instruction
    if (breakpoint)     return 4'd3;  // Breakpoint
    if (load_mis)       return 4'd4;  // Load address misaligned
    if (load_access)    return 4'd5;  // Load access fault
    if (store_mis)      return 4'd6;  // Store address misaligned
    if (store_access)   return 4'd7;  // Store access fault
    if (ecall)          return 4'd11; // Environment call M-mode
    return 4'd15;                     // No exception
endfunction
```

### Trap Entry

```systemverilog
// Exception oluştuğunda
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        mepc   <= '0;
        mcause <= '0;
        mtval  <= '0;
    end else if (exception_valid) begin
        // Save PC
        mepc <= exception_pc;

        // Save cause (exception code)
        mcause <= {1'b0, 27'b0, exception_code};

        // Save trap value
        case (exception_code)
            EXC_INSTR_ADDR_MIS:  mtval <= exception_pc;
            EXC_INSTR_ACC_FAULT: mtval <= exception_pc;
            EXC_ILLEGAL_INSTR:   mtval <= exception_instr;
            EXC_LOAD_ADDR_MIS:   mtval <= exception_addr;
            EXC_LOAD_ACC_FAULT:  mtval <= exception_addr;
            EXC_STORE_ADDR_MIS:  mtval <= exception_addr;
            EXC_STORE_ACC_FAULT: mtval <= exception_addr;
            default:             mtval <= '0;
        endcase
    end
end
```

---

## Pipeline Entegrasyonu

### Exception Propagation

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                        EXCEPTION FLOW IN PIPELINE                                │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   FETCH ─────► DECODE ─────► EXECUTE ─────► MEMORY ─────► WRITEBACK             │
│     │            │              │             │              │                   │
│     │            │              │             │              │                   │
│     ▼            ▼              ▼             ▼              ▼                   │
│  ┌──────┐    ┌──────┐      ┌──────┐      ┌──────┐      ┌──────┐                 │
│  │Instr │    │Illegal│     │ (none│      │Load/ │      │      │                 │
│  │Addr  │    │Instr │      │ usually)    │Store │      │Commit│                 │
│  │Fault │    │Break │      │      │      │Fault │      │      │                 │
│  └──────┘    └──────┘      └──────┘      └──────┘      └──────┘                 │
│     │            │              │             │              │                   │
│     │            │              │             │              │                   │
│     └────────────┴──────────────┴─────────────┴──────────────┘                   │
│                                  │                                               │
│                                  ▼                                               │
│                          ┌─────────────┐                                        │
│                          │  EXCEPTION  │                                        │
│                          │  RESOLVER   │                                        │
│                          └──────┬──────┘                                        │
│                                 │                                               │
│                                 ▼                                               │
│                          ┌─────────────┐                                        │
│                          │ TRAP ENTRY  │                                        │
│                          │ (CSR write) │                                        │
│                          └──────┬──────┘                                        │
│                                 │                                               │
│                                 ▼                                               │
│                          ┌─────────────┐                                        │
│                          │ FLUSH PIPE  │                                        │
│                          │ Jump mtvec  │                                        │
│                          └─────────────┘                                        │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### Exception Register

Pipeline stage'ler arasında exception bilgisi taşınır:

```systemverilog
typedef struct packed {
    logic        valid;       // Exception aktif
    logic [3:0]  cause;       // Exception code
    logic [31:0] pc;          // Exception PC
    logic [31:0] tval;        // Trap value
} exception_t;

// Pipeline register
exception_t ex_exception_q, mem_exception_q;
```

### Precise Exception

RISC-V precise exception gerektirir:

```systemverilog
// Exception olan instruction'dan önceki tüm instruction'lar
// commit edilmiş olmalı
// Sonrakiler flush edilmeli

always_comb begin
    if (exception_valid) begin
        // Flush younger instructions
        flush_if = 1'b1;
        flush_id = 1'b1;
        flush_ex = 1'b1;

        // Exception instruction commit edilmez
        mem_commit = 1'b0;
    end
end
```

---

## Kullanım Örnekleri

### Exception Handler

```systemverilog
module exception_handler
  import ceres_param::*;
(
    input  logic        clk_i,
    input  logic        rst_ni,

    // Exception inputs from pipeline
    input  logic        i_fetch_fault,
    input  logic        i_illegal_instr,
    input  logic        i_load_fault,
    input  logic        i_store_fault,
    input  logic [31:0] i_pc,
    input  logic [31:0] i_addr,
    input  logic [31:0] i_instr,

    // Exception output
    output logic        o_exception,
    output logic [3:0]  o_cause,
    output logic [31:0] o_tval
);

`include "exception_priority.svh"

    // Priority-based exception selection
    always_comb begin
        o_exception = 1'b0;
        o_cause     = '0;
        o_tval      = '0;

        if (i_fetch_fault) begin
            o_exception = 1'b1;
            o_cause     = PRIORITY_INSTR_ACCESS_FAULT[3:0];
            o_tval      = i_pc;
        end else if (i_illegal_instr) begin
            o_exception = 1'b1;
            o_cause     = PRIORITY_ILLEGAL_INSTR[3:0];
            o_tval      = i_instr;
        end else if (i_load_fault) begin
            o_exception = 1'b1;
            o_cause     = PRIORITY_LOAD_ACCESS_FAULT[3:0];
            o_tval      = i_addr;
        end else if (i_store_fault) begin
            o_exception = 1'b1;
            o_cause     = PRIORITY_STORE_ACCESS_FAULT[3:0];
            o_tval      = i_addr;
        end
    end

endmodule
```

### Test Code

```c
// Exception test (C code)

void test_illegal_instruction() {
    // Illegal instruction - should trap
    asm volatile(".word 0x00000000");
}

void test_load_misaligned() {
    volatile int* ptr = (int*)0x80000001;  // Misaligned
    int val = *ptr;  // Should trap
}

void test_store_access_fault() {
    volatile int* ptr = (int*)0x00000000;  // Invalid region
    *ptr = 0xDEADBEEF;  // Should trap
}
```

---

## Özet

`exception_priority.svh` dosyası:

1. **Priority Definition**: RISC-V exception öncelikleri
2. **Exception Types**: 11 farklı exception tipi
3. **Trap Handling**: CSR kayıtları (mepc, mcause, mtval)
4. **Precise Exception**: Pipeline flush ve recovery
5. **Configurable**: Parametre ile özelleştirilebilir

Bu dosya, CERES RISC-V işlemcisinin exception handling mekanizmasının temelini oluşturur.
# Fetch Log - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Log Formatı](#log-formatı)
3. [Sinyaller](#sinyaller)
4. [Kullanım](#kullanım)
5. [Debug Senaryoları](#debug-senaryoları)

---

## Genel Bakış

### Amaç

`fetch_log.svh` dosyası, **Fetch stage** debug ve trace çıktıları için log formatlarını tanımlar. I-Cache erişimleri, branch prediction sonuçları ve pipeline stall'ları izlenebilir.

### Dosya Konumu

```
rtl/include/fetch_log.svh
```

### Aktivasyon

```bash
# Makefile ile
make run T=test LOG_FETCH=1

# Verilator define
+define+LOG_FETCH
```

---

## Log Formatı

### Temel Log Yapısı

```systemverilog
`ifdef LOG_FETCH

    // Fetch trace output
    always_ff @(posedge clk_i) begin
        if (fetch_valid && !stall) begin
            $display("[FETCH] PC=%08x INSTR=%08x %s @ %0t",
                     pc,
                     instruction,
                     is_compressed ? "C" : "I",
                     $time);
        end
    end

`endif
```

### Örnek Çıktı

```
[FETCH] PC=80000000 INSTR=00000297 I @ 1000
[FETCH] PC=80000004 INSTR=02028293 I @ 1010
[FETCH] PC=80000008 INSTR=00010137 I @ 1020
[FETCH] PC=8000000c INSTR=f1402573 I @ 1030
[FETCH] PC=80000010 INSTR=30200073 I @ 1040
```

---

## Sinyaller

### İzlenen Sinyaller

```systemverilog
// Fetch stage signals
logic [31:0] pc;              // Current program counter
logic [31:0] instruction;     // Fetched instruction
logic        fetch_valid;     // Fetch successful
logic        is_compressed;   // Compressed instruction
logic        stall;           // Pipeline stall
logic        flush;           // Pipeline flush

// I-Cache signals
logic        icache_hit;      // Cache hit
logic        icache_miss;     // Cache miss
logic        icache_busy;     // Cache busy

// Branch prediction
logic        bp_taken;        // Predicted taken
logic [31:0] bp_target;       // Predicted target
```

### Log Seviyeleri

```systemverilog
// Basic fetch log
`ifdef LOG_FETCH
    // PC, instruction logging
`endif

// Verbose fetch log
`ifdef LOG_FETCH_VERBOSE
    // Cache hit/miss
    // Branch prediction details
    // Stall reasons
`endif
```

---

## Kullanım

### Basit Fetch Log

```systemverilog
`include "fetch_log.svh"

module fetch_stage
  import ceres_param::*;
(
    input  logic        clk_i,
    // ...
);

`ifdef LOG_FETCH
    always_ff @(posedge clk_i) begin
        if (o_valid) begin
            $display("[FETCH] PC=%08x INSTR=%08x @ %0t",
                     o_pc, o_instr, $time);
        end
    end
`endif

endmodule
```

### Detaylı Fetch Log

```systemverilog
`ifdef LOG_FETCH_VERBOSE

    always_ff @(posedge clk_i) begin
        // Cache durumu
        if (icache_req) begin
            if (icache_hit) begin
                $display("[FETCH] ICACHE HIT  PC=%08x @ %0t", pc, $time);
            end else begin
                $display("[FETCH] ICACHE MISS PC=%08x @ %0t", pc, $time);
            end
        end

        // Branch prediction
        if (bp_valid) begin
            $display("[FETCH] BP %s target=%08x @ %0t",
                     bp_taken ? "TAKEN" : "NOT_TAKEN",
                     bp_target, $time);
        end

        // Stall nedeni
        if (stall) begin
            $display("[FETCH] STALL reason=%s @ %0t",
                     stall_reason.name(), $time);
        end

        // Flush
        if (flush) begin
            $display("[FETCH] FLUSH redirect=%08x @ %0t",
                     redirect_pc, $time);
        end
    end

`endif
```

---

## Debug Senaryoları

### 1. I-Cache Miss Analizi

```systemverilog
// Cache miss sayısını takip et
`ifdef LOG_FETCH
    int icache_miss_count = 0;
    int icache_hit_count = 0;

    always_ff @(posedge clk_i) begin
        if (icache_req) begin
            if (icache_hit) begin
                icache_hit_count <= icache_hit_count + 1;
            end else begin
                icache_miss_count <= icache_miss_count + 1;
                $display("[FETCH] MISS #%0d PC=%08x @ %0t",
                         icache_miss_count, pc, $time);
            end
        end
    end

    final begin
        $display("[FETCH] Total: Hits=%0d Misses=%0d Rate=%.2f%%",
                 icache_hit_count, icache_miss_count,
                 100.0 * icache_hit_count / (icache_hit_count + icache_miss_count));
    end
`endif
```

### 2. Branch Misprediction

```systemverilog
`ifdef LOG_FETCH
    always_ff @(posedge clk_i) begin
        if (branch_resolve) begin
            if (bp_mispredicted) begin
                $display("[FETCH] MISPREDICT PC=%08x pred=%08x actual=%08x @ %0t",
                         branch_pc, bp_target, actual_target, $time);
            end
        end
    end
`endif
```

### 3. Pipeline Stall İzleme

```systemverilog
`ifdef LOG_FETCH
    int stall_cycles = 0;

    always_ff @(posedge clk_i) begin
        if (stall) begin
            stall_cycles <= stall_cycles + 1;
            if (stall_cycles > 100) begin
                $warning("[FETCH] Long stall: %0d cycles @ %0t",
                         stall_cycles, $time);
            end
        end else begin
            if (stall_cycles > 0) begin
                $display("[FETCH] Stall ended after %0d cycles @ %0t",
                         stall_cycles, $time);
            end
            stall_cycles <= 0;
        end
    end
`endif
```

---

## İlgili Dosyalar

| Dosya | Açıklama |
|-------|----------|
| `rtl/core/stage01_fetch/` | Fetch stage modülleri |
| `rtl/core/mmu/cache.sv` | I-Cache implementasyonu |
| `writeback_log.svh` | Commit trace (karşılaştırma için) |

---

## Özet

`fetch_log.svh` dosyası:

1. **PC/Instruction Log**: Temel fetch izleme
2. **Cache Analysis**: Hit/miss istatistikleri
3. **Branch Debug**: Misprediction izleme
4. **Stall Analysis**: Pipeline stall nedenleri
5. **Conditional Compilation**: `ifdef` ile kontrol

Bu dosya, fetch stage debug ve performans analizi için kullanılır.
# Writeback Log - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Spike Uyumlu Commit Trace](#spike-uyumlu-commit-trace)
3. [Log Formatları](#log-formatları)
4. [PASS/FAIL Algılama](#passfail-algılama)
5. [Konata Pipeline Trace](#konata-pipeline-trace)
6. [CSR Trace](#csr-trace)
7. [Kullanım ve Entegrasyon](#kullanım-ve-entegrasyon)

---

## Genel Bakış

### Amaç

`writeback_log.svh` dosyası, **Writeback stage** için kapsamlı trace ve log mekanizmalarını tanımlar. Özellikle **Spike simulator** ile karşılaştırılabilir commit trace formatı sağlar.

### Dosya Konumu

```
rtl/include/writeback_log.svh
```

### Temel Özellikler

| Özellik | Açıklama |
|---------|----------|
| **Spike Format** | `core 0: PC (INSTR) rd DATA` |
| **PASS/FAIL** | Otomatik test sonucu algılama |
| **Konata** | Pipeline visualizer desteği |
| **CSR Trace** | CSR register değişiklikleri |

---

## Spike Uyumlu Commit Trace

### Format Tanımı

Spike simulator'ün commit trace formatı:

```
core   0: 0x80000000 (0x00000297) x5  0x80000000
core   0: 0x80000004 (0x02028293) x5  0x80000028
core   0: 0x80000008 (0x30529073)
```

**Format:** `core <hart_id>: 0x<PC> (0x<INSTR>) [x<rd> 0x<DATA>]`

### Implementasyon

```systemverilog
`ifdef LOG_COMMIT

    // Spike-compatible commit trace
    always_ff @(posedge clk_i) begin
        if (commit_valid && !flush) begin
            if (rd_we && rd_addr != 5'd0) begin
                // Register write - show rd and value
                $display("core   0: 0x%08x (0x%08x) x%-2d 0x%08x",
                         commit_pc,
                         commit_instr,
                         rd_addr,
                         rd_data);
            end else begin
                // No register write (stores, branches, etc.)
                $display("core   0: 0x%08x (0x%08x)",
                         commit_pc,
                         commit_instr);
            end
        end
    end

`endif
```

### Spike Karşılaştırma

```bash
# RTL simülasyonu
make run T=rv32ui-p-add LOG_COMMIT=1 > rtl_trace.log

# Spike simülasyonu
spike --log-commits rv32ui-p-add > spike_trace.log

# Karşılaştırma
diff rtl_trace.log spike_trace.log
```

---

## Log Formatları

### Temel Commit Log

```systemverilog
`ifdef LOG_COMMIT
    always_ff @(posedge clk_i) begin
        if (commit_valid) begin
            // Standard format
            $display("core   0: 0x%08x (0x%08x) x%-2d 0x%08x",
                     pc, instr, rd, data);
        end
    end
`endif
```

### Genişletilmiş Log

```systemverilog
`ifdef LOG_COMMIT_VERBOSE

    always_ff @(posedge clk_i) begin
        if (commit_valid) begin
            // Instruction disassembly
            $display("[WB] PC=%08x %s rd=x%0d val=%08x",
                     pc,
                     disasm(instr),  // Disassembly function
                     rd,
                     data);

            // Memory operations
            if (is_load) begin
                $display("[WB]   LOAD addr=%08x data=%08x",
                         mem_addr, load_data);
            end
            if (is_store) begin
                $display("[WB]   STORE addr=%08x data=%08x",
                         mem_addr, store_data);
            end
        end
    end

`endif
```

### Memory Trace

```systemverilog
`ifdef LOG_MEM

    always_ff @(posedge clk_i) begin
        // Load commit
        if (load_commit) begin
            $display("MEM: LOAD  addr=%08x data=%08x size=%0d",
                     mem_addr, load_data, mem_size);
        end

        // Store commit
        if (store_commit) begin
            $display("MEM: STORE addr=%08x data=%08x size=%0d",
                     mem_addr, store_data, mem_size);
        end
    end

`endif
```

---

## PASS/FAIL Algılama

### RISC-V Test Signature

RISC-V testleri sonucu `tohost` adresine yazarak bildirir:

```systemverilog
// Test result detection
localparam TOHOST_ADDR = 32'h8000_1000;  // Configurable

`ifdef LOG_COMMIT

    always_ff @(posedge clk_i) begin
        // tohost write detection
        if (store_commit && mem_addr == TOHOST_ADDR) begin
            if (store_data == 32'h0000_0001) begin
                $display("*** PASS ***");
                $display("Test completed successfully @ %0t", $time);
                $finish(0);
            end else if (store_data != 32'h0) begin
                $display("*** FAIL ***");
                $display("Test failed with code: %0d @ %0t",
                         store_data >> 1, $time);
                $finish(1);
            end
        end
    end

`endif
```

### Benchmark Sonucu Algılama

```systemverilog
`ifdef SIM_UART_MONITOR

    // UART output monitoring
    string uart_buffer;

    always_ff @(posedge clk_i) begin
        if (uart_tx_valid) begin
            uart_buffer = {uart_buffer, string'(uart_tx_data)};

            // Check for PASS/FAIL patterns
            if (uart_buffer.find("PASS") != -1) begin
                $display("*** PASS detected in UART output ***");
                $finish(0);
            end
            if (uart_buffer.find("FAIL") != -1) begin
                $display("*** FAIL detected in UART output ***");
                $finish(1);
            end

            // CoreMark result pattern
            if (uart_buffer.find("CoreMark 1.0 :") != -1) begin
                $display("*** CoreMark completed ***");
            end
        end
    end

`endif
```

### Write to TOHOST Detection

```systemverilog
// Detailed tohost analysis
always_ff @(posedge clk_i) begin
    if (store_commit && mem_addr == TOHOST_ADDR) begin
        case (store_data)
            32'h0000_0001: begin
                $display("[TEST] PASS @ cycle %0d", cycle_count);
            end
            32'h0000_0000: begin
                // Ignore zero write
            end
            default: begin
                // Fail with test number
                $display("[TEST] FAIL test_num=%0d @ cycle %0d",
                         store_data >> 1, cycle_count);
            end
        endcase
    end
end
```

---

## Konata Pipeline Trace

### Konata Format

Konata pipeline visualizer için özel trace format:

```systemverilog
`ifdef KONATA_TRACER

    integer konata_file;

    initial begin
        konata_file = $fopen("pipeline.log", "w");
        $fwrite(konata_file, "Kanata\t0004\n");
    end

    always_ff @(posedge clk_i) begin
        // Instruction fetch
        if (if_valid) begin
            $fwrite(konata_file, "I\t%0d\t%0d\t0\n",
                    instr_id, cycle_count);
        end

        // Stage transitions
        if (id_valid) begin
            $fwrite(konata_file, "S\t%0d\t%0d\t%s\n",
                    instr_id, cycle_count, "D");
        end

        if (ex_valid) begin
            $fwrite(konata_file, "S\t%0d\t%0d\t%s\n",
                    instr_id, cycle_count, "E");
        end

        if (mem_valid) begin
            $fwrite(konata_file, "S\t%0d\t%0d\t%s\n",
                    instr_id, cycle_count, "M");
        end

        // Instruction commit
        if (commit_valid) begin
            $fwrite(konata_file, "R\t%0d\t%0d\t0\n",
                    instr_id, cycle_count);
        end

        // Instruction flush
        if (flush_valid) begin
            $fwrite(konata_file, "R\t%0d\t%0d\t1\n",
                    instr_id, cycle_count);
        end
    end

    final begin
        $fclose(konata_file);
    end

`endif
```

### Konata Komutları

| Komut | Format | Açıklama |
|-------|--------|----------|
| I | `I id cycle 0` | Instruction issue |
| S | `S id cycle stage` | Stage transition |
| R | `R id cycle flush` | Retire (0=commit, 1=flush) |
| L | `L id cycle text` | Label (optional) |

---

## CSR Trace

### CSR Write Logging

```systemverilog
`ifdef LOG_CSR

    always_ff @(posedge clk_i) begin
        if (csr_we) begin
            $display("[CSR] WRITE %s (0x%03x) = 0x%08x @ PC=%08x",
                     csr_name(csr_addr),
                     csr_addr,
                     csr_wdata,
                     commit_pc);
        end
    end

    function automatic string csr_name(input logic [11:0] addr);
        case (addr)
            12'h300: return "mstatus";
            12'h301: return "misa";
            12'h304: return "mie";
            12'h305: return "mtvec";
            12'h340: return "mscratch";
            12'h341: return "mepc";
            12'h342: return "mcause";
            12'h343: return "mtval";
            12'h344: return "mip";
            12'hF11: return "mvendorid";
            12'hF12: return "marchid";
            12'hF13: return "mimpid";
            12'hF14: return "mhartid";
            12'hB00: return "mcycle";
            12'hB02: return "minstret";
            default: return $sformatf("csr_%03x", addr);
        endcase
    endfunction

`endif
```

### Exception/Interrupt Logging

```systemverilog
`ifdef LOG_EXCEPTION

    always_ff @(posedge clk_i) begin
        if (exception_valid) begin
            $display("[TRAP] EXCEPTION cause=%s (%0d) PC=%08x tval=%08x",
                     exception_name(mcause),
                     mcause,
                     mepc,
                     mtval);
        end

        if (interrupt_valid) begin
            $display("[TRAP] INTERRUPT cause=%0d PC=%08x",
                     mcause[30:0],
                     mepc);
        end

        if (mret_valid) begin
            $display("[TRAP] MRET return to PC=%08x",
                     mepc);
        end
    end

`endif
```

---

## Kullanım ve Entegrasyon

### Makefile Entegrasyonu

```makefile
# Log kontrolleri
LOG_COMMIT ?= 0
LOG_CSR ?= 0
LOG_MEM ?= 0
KONATA_TRACER ?= 0

# Verilator defines
ifeq ($(LOG_COMMIT),1)
    VFLAGS += +define+LOG_COMMIT
endif

ifeq ($(KONATA_TRACER),1)
    VFLAGS += +define+KONATA_TRACER +define+COMMIT_TRACER
endif
```

### Kullanım Örnekleri

```bash
# ISA test with commit trace
make run T=rv32ui-p-add LOG_COMMIT=1

# Pipeline visualization
make run T=rv32ui-p-add KONATA_TRACER=1

# Full debug mode
make run T=test LOG_COMMIT=1 LOG_CSR=1 LOG_MEM=1

# Benchmark with UART monitoring
make cm SIM_UART_MONITOR=1 LOG_COMMIT=1
```

### Log Dosyaları

| Log | Dosya | İçerik |
|-----|-------|--------|
| Commit | stdout/commit.log | Spike-uyumlu trace |
| Pipeline | pipeline.log | Konata format |
| UART | uart.log | UART çıktısı |

---

## Performans Etkisi

### Log Overhead

| Mode | Overhead | Kullanım |
|------|----------|----------|
| No logging | 0% | Production |
| LOG_COMMIT | ~5% | Debug |
| KONATA_TRACER | ~10% | Pipeline analysis |
| All logs | ~20% | Full debug |

### SIM_FAST Mode

```systemverilog
`ifdef SIM_FAST
    // Tüm log'lar devre dışı
    // Maksimum simülasyon hızı
`else
    // Normal log modları aktif
`endif
```

---

## Özet

`writeback_log.svh` dosyası:

1. **Spike Format**: `core 0: PC (INSTR) rd DATA`
2. **PASS/FAIL**: tohost ve UART izleme
3. **Konata**: Pipeline visualizer desteği
4. **CSR Trace**: Register değişiklikleri
5. **Configurable**: Makefile ile kontrol

Bu dosya, CERES RISC-V işlemcisinin doğrulama ve debug altyapısının temelini oluşturur.
