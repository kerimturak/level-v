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
