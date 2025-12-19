# CERES RISC-V — SystemVerilog Define Reference

## 📋 İsimlendirme Kuralları

| Prefix | Anlam | Varsayılan | Örnek |
|--------|-------|------------|-------|
| `LOG_*` | Loglama özellikleri | KAPALI | `LOG_COMMIT`, `LOG_BP` |
| `TRACE_*` | Trace özellikleri | KAPALI | `KONATA_TRACER` |
| `SIM_*` | Simülasyon kontrolleri | KAPALI | `SIM_FAST`, `SIM_UART_MONITOR` |
| `FEAT_*` | RTL feature'ları | Değişken | `FEAT_WALLACE_SINGLE` |

## 📊 Define Tablosu

### Log Kontrolleri (varsayılan KAPALI, `+define+` ile aç)

| Define | Dosya | Açıklama |
|--------|-------|----------|
| `LOG_COMMIT` | writeback_log.svh | Spike-compatible commit trace |
| `LOG_PIPELINE` | pipeline_logger.sv | Konata pipeline trace file |
| `LOG_RAM` | wrapper_ram.sv | RAM initialization messages |
| `LOG_UART` | uart_tx.sv | UART TX file logging |
| `LOG_BP` | gshare_bp.sv | Branch predictor statistics |
| `LOG_BP_VERBOSE` | gshare_bp.sv | Per-branch detailed logging |

### Trace Kontrolleri (varsayılan KAPALI)

| Define | Dosya | Açıklama |
|--------|-------|----------|
| `KONATA_TRACER` | cpu.sv | Pipeline visualizer (Konata format) |
| `TRACE_INTERNAL` | fetch, cpu, etc. | Internal debug signal structs |

### Simülasyon Kontrolleri

| Define | Dosya | Açıklama |
|--------|-------|----------|
| `SIM_FAST` | ceres_defines.svh | Fast mode (all logs disabled) |
| `SIM_UART_MONITOR` | uart_tx.sv | UART monitoring + auto-stop |
| `SIM_COVERAGE` | - | Coverage collection |

### Feature Flags

| Define | Dosya | Açıklama |
|--------|-------|----------|
| `FEAT_WALLACE_SINGLE` | alu.sv | Single-cycle Wallace multiplier |
| `FEAT_WALLACE_MULTI` | alu.sv | Multi-cycle Wallace multiplier |
| `FEAT_DSP_MUL` | alu.sv | DSP block multiplier |

### Platform

| Define | Dosya | Açıklama |
|--------|-------|----------|
| `VERILATOR` | çeşitli | Verilator-specific code paths |

## 🚀 Kullanım Profilleri

### CoreMark / Benchmark (Maksimum Hız)
```bash
make cm SIM_FAST=1 LOG_BP=1 SIM_UART_MONITOR=1
```
Veya doğrudan:
```verilog
+define+SIM_FAST
+define+LOG_BP
+define+SIM_UART_MONITOR
```

### ISA Test (Debug)
```bash
make isa LOG_COMMIT=1 KONATA_TRACER=1
```
Veya:
```verilog
+define+LOG_COMMIT
+define+KONATA_TRACER
```

### Full Debug (tek test)
```bash
make t T=rv32ui-p-add LOG_COMMIT=1 LOG_PIPELINE=1 KONATA_TRACER=1 LOG_BP=1
```

## 📁 Merkezi Kontrol

Tüm define'lar `rtl/include/ceres_defines.svh` dosyasından kontrol edilir.

### Backward Compatibility
Eski isimler hala desteklenir:
```
FAST_SIM          → SIM_FAST
KONATA_TRACE      → KONATA_TRACER
COMMIT_TRACER         → TRACE_INTERNAL
BP_LOGGER_EN      → LOG_BP
BP_VERBOSE_LOG    → LOG_BP_VERBOSE
CERES_UART_TX_MONITOR → SIM_UART_MONITOR
WALLACE_SINGLE_CYCLE  → FEAT_WALLACE_SINGLE
```

## 📊 JSON Config Entegrasyonu

`script/config/tests/*.json` dosyalarındaki `defines` bölümü:

```json
{
  "defines": {
    "SIM_FAST": true,
    "LOG_COMMIT": false,
    "LOG_BP": true,
    "KONATA_TRACER": false,
    "SIM_UART_MONITOR": true
  }
}
```

### Mevcut Konfigürasyonlar

| Config | SIM_FAST | LOG_COMMIT | LOG_BP | KONATA_TRACER | Açıklama |
|--------|----------|------------|--------|--------------|----------|
| `isa` | ❌ | ✅ | ❌ | ✅ | ISA testleri |
| `arch` | ❌ | ✅ | ❌ | ✅ | Arch testleri |
| `bench` | ✅ | ❌ | ✅ | ❌ | Benchmarklar |
| `coremark` | ✅ | ❌ | ✅ | ❌ | CoreMark |
| `imperas` | ❌ | ✅ | ❌ | ❌ | Imperas testleri |

## 🔧 Makefile Kullanımı

```bash
# Log kontrolü
make run T=test LOG_COMMIT=1 LOG_PIPELINE=1

# Trace kontrolü  
make run T=test KONATA_TRACER=1

# Simülasyon kontrolü
make cm SIM_FAST=1 SIM_UART_MONITOR=1

# JSON config kullanımı
make run TEST_CONFIG=bench

# Mevcut config'i göster
make show-config

# Config listesi
make list-configs
```
