// ============================================================================
// CERES RISC-V — Central Feature Defines
// ============================================================================
// Bu dosya tüm RTL tarafından include edilir.
// Makefile/JSON config'den gelen +define+ ifadeleri bu dosyayı override eder.
//
// Kullanım:
//   make run LOG_COMMIT=1 KONATA_TRACER=1    # Trace loglarını aç
//   make run SIM_FAST=1                       # Hızlı mod (loglar kapalı)
// ============================================================================

// ============================================================================
// TRACE & LOG KONTROLLERI (varsayılan KAPALI, +define+ ile aç)
// ============================================================================
// COMMIT_TRACER : Pipe register'larda trace bilgisi taşı (LOG_COMMIT için gerekli)
// KONATA_TRACER : KONATA pipeline visualizer (konata_logger.sv + cpu.sv)
// LOG_COMMIT    : Spike-compatible commit trace (writeback_log.svh)
// LOG_RAM       : RAM initialization messages (wrapper_ram.sv)
// LOG_UART      : UART TX file logging (uart_tx.sv)
// LOG_BP        : Branch predictor statistics (gshare_bp.sv)
// LOG_BP_VERBOSE: Detailed per-branch logging (gshare_bp.sv)
// LOG_CACHE     : Cache request/response table logging (cache_logger.sv)
// LOG_LDST      : LD/ST buffer event logging (merge/forward/block/bypass)

// ============================================================================
// MINIMAL SOC - Fast Simulation Mode
// ============================================================================
// MINIMAL_SOC: Benchmark modunda (CoreMark vb.) kaynak kullanımını minimize et
// 
// Bu modda:
//   - Cache: 2KB I-Cache + 2KB D-Cache (8KB yerine)
//   - Branch Predictor: PHT=64, BTB=32, GHR=8 (512/256/24 yerine)
//   - Sadece CPU + RAM + UART + Timer + CLINT aktif
//
// Faydaları:
//   - Verilator compile süresi ~%40-50 azalır
//   - Simülasyon hızı ~%20-30 artar
//   - CoreMark gibi küçük benchmarklar için yeterli
//
// Kullanım: 
//   make cm_quick MINIMAL_SOC=1
//   make verilate MINIMAL_SOC=1 FAST_SIM=1


// ============================================================================
// FEATURE FLAGS
// ============================================================================
// Cache implementation selection
//`define USE_UNIFIED_CACHE // Unified cache module (cache.sv with icache/dcache)
//`define USE_STANDALONE_DCACHE // Standalone dcache module (dcache.sv - writeback only)

// Multiplier implementation (sadece biri aktif olmalı)
// Priority: PIPELINED_MUL > WALLACE_SINGLE > DSP_MUL > Sequential
`define FEAT_PIPELINED_MUL // Pipelined multiplier (2 cycles, better timing)
//`define LOG_CACHE_DEBUG // Cache debug logging (use LOG_CACHE=1 in Makefile)
// Breaks 32x32 into 4x 8x32 muls for reduced logic depth
//`define FEAT_WALLACE_SINGLE // Tek cycle Wallace tree (deep comb logic)
//`define FEAT_WALLACE_MULTI   // Multi-cycle Wallace tree
//`define FEAT_DSP_MUL         // DSP block multiplier

// Division implementation
`define FEAT_PIPELINED_DIV // Pipelined division (2 bits/cycle, better timing)
//`define SYNTHESIS // Pipelined division (2 bits/cycle, better timing)
// If not defined, uses original sequential (1 bit/cycle)

`ifdef SYNTHESIS
`define MINIMAL_SOC
`endif
// ============================================================================
// SIMULATION CONTROLS
// ============================================================================
// SIM_FAST         : Hızlı mod, logları kapatır
// SIM_UART_MONITOR : UART çıktı izleme + threshold'da durdurma

// ============================================================================
// IMPLICIT DEPENDENCIES
// ============================================================================
// LOG_COMMIT kullanıyorsan COMMIT_TRACER gerekli (pipe'da fe_tracer için)
`ifndef SYNTHESIS
`ifdef LOG_COMMIT
`ifndef COMMIT_TRACER
`define COMMIT_TRACER
`endif
`endif

// KONATA_TRACER kullanıyorsan COMMIT_TRACER gerekli (sn/inst için)
`ifdef KONATA_TRACER
`ifndef COMMIT_TRACER
`define COMMIT_TRACER
`endif
`endif

// ============================================================================
// BACKWARD COMPATIBILITY
// ============================================================================
`ifdef FAST_SIM
`define SIM_FAST
`endif

`ifdef KONATA_TRACE
`define KONATA_TRACER
`endif

`ifdef BP_LOGGER_EN
`define LOG_BP
`endif

`ifdef CERES_UART_TX_MONITOR
`define SIM_UART_MONITOR
`endif
`endif
