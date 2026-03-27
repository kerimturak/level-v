// ============================================================================
// Level RISC-V — Central Feature Defines
// ============================================================================
// This file is included by all RTL.
// +define+ directives from the Makefile/JSON config override this file.
//
// Usage:
//   make run LOG_COMMIT=1 KONATA_TRACER=1    # Enable trace logs
//   make run SIM_FAST=1                       # Fast mode (logs off)
// ============================================================================

// ============================================================================
// TRACE & LOG CONTROLS (default OFF; enable with +define+)
// ============================================================================
// COMMIT_TRACER : Carry trace info in pipeline registers (required for LOG_COMMIT)
// KONATA_TRACER : KONATA pipeline visualizer (konata_logger.sv + cpu.sv)
// LOG_COMMIT    : Spike-compatible commit trace (writeback_log.svh)
// LOG_RAM       : RAM initialization messages (wrapper_ram.sv)
// LOG_UART      : UART TX file logging (uart_tx.sv)
// LOG_BP        : Branch predictor statistics (gshare_bp.sv)
// LOG_BP_VERBOSE: Detailed per-branch logging (gshare_bp.sv)
// LOG_CACHE     : Cache request/response table logging (cache_logger.sv)

// ============================================================================
// MINIMAL SOC - Fast Simulation Mode
// ============================================================================
// MINIMAL_SOC: In benchmark mode (CoreMark, etc.) minimize resource usage
// 
// In this mode:
//   - Cache: 2KB I-Cache + 2KB D-Cache (instead of 8KB)
//   - Branch Predictor: PHT=64, BTB=32, GHR=8 (instead of 512/256/24)
//   - Only CPU + RAM + UART + Timer + CLINT active
//
// Benefits:
//   - Verilator compile time drops ~40-50%
//   - Simulation speed increases ~20-30%
//   - Sufficient for small benchmarks like CoreMark
//
// Usage: 
//   make run_coremark COREMARK_ITERATIONS=0 SIM_FAST=1 MINIMAL_SOC=1 TRACE=0 MAX_CYCLES=2000000
//   make verilate MINIMAL_SOC=1 SIM_FAST=1


// ============================================================================
// FEATURE FLAGS
// ============================================================================
// Cache implementation selection
//`define USE_UNIFIED_CACHE // Unified cache module (cache.sv with icache/dcache)
//`define USE_STANDALONE_DCACHE // Standalone dcache module (dcache.sv - writeback only)
`ifndef USE_L2_CACHE
`define USE_L2_CACHE
`endif

// Multiplier implementation (only one must be active)
// Priority: PIPELINED_MUL > WALLACE_SINGLE > DSP_MUL > Sequential
`define FEAT_PIPELINED_MUL // Pipelined multiplier (2 cycles, better timing)
//`define LOG_CACHE_DEBUG // Cache debug logging (use LOG_CACHE=1 in Makefile)
// Breaks 32x32 into 4x 8x32 muls for reduced logic depth
//`define FEAT_WALLACE_SINGLE // Single-cycle Wallace tree (deep comb logic)
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
// SIM_FAST         : Fast mode; turns logs off
// SIM_UART_MONITOR : UART output monitoring + stop at threshold

// ============================================================================
// IMPLICIT DEPENDENCIES
// ============================================================================
// If you use LOG_COMMIT, COMMIT_TRACER is required (fe_tracer in the pipe)
`ifndef SYNTHESIS
`ifdef LOG_COMMIT
`ifndef COMMIT_TRACER
`define COMMIT_TRACER
`endif
`endif

// If you use KONATA_TRACER, COMMIT_TRACER is required (sn/inst)
`ifdef KONATA_TRACER
`ifndef COMMIT_TRACER
`define COMMIT_TRACER
`endif
`endif

`endif
