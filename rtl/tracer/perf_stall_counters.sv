/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

================================================================================
Pipeline perf (enable: +define+LOG_PERF_STALL or make LOG_PERF_STALL=1)

Stall cycles: cpu stall_cause != NO_STALL (priority per cpu.sv).

Flush events: once per cycle when the front-end / EX is squashed (priority order
below). de_flush_en / ex_flush_en match the masked hazard_unit outputs in cpu.

cycles_clk_total: all posedge clk_i (incl. reset). cycles_active: rst high only,
used as denominator for stall %% / flush statistics.
================================================================================
*/
`timescale 1ns / 1ps
`include "level_defines.svh"

module perf_stall_counters
  import level_param::*;
(
    input logic       clk_i,
    input logic       rst_ni,
    input stall_e     stall_cause,
    input logic       fencei_flush_i,
    input logic [1:0] priority_flush_i,
  input logic       de_flush_en_i,
  input logic       ex_flush_en_i,
  // USE_L2_CACHE: nbmbmp_l2_cache.l2_miss_busy_o — L2 miss service cycles only (not stall_cause).
  input logic       l2_miss_busy_i
);

`ifdef LOG_PERF_STALL

  // Every posedge clk_i for the whole run (not cleared on CPU rst_ni)
  logic [63:0] cycles_clk_total;
  // CPU out of reset — denominator for stall % / flush-event %
  logic [63:0] cycles_active;
  logic [63:0] cycles_stall_total;
  // Cycles where stall and (any counted) flush both occurred (overlap diagnostics)
  logic [63:0] cycles_stall_with_flush;
  logic [63:0] cnt_load_raw;
  logic [63:0] cnt_imiss;
  logic [63:0] cnt_dmiss;
  logic [63:0] cnt_alu;
  logic [63:0] cnt_fencei;
  logic [63:0] cnt_l2_miss_cycles;

  // Pipeline squashes (effective after stall masking in cpu.sv)
  logic [63:0] flush_events_total;
  logic [63:0] cnt_flush_ex_trap;
  logic [63:0] cnt_flush_de_trap;
  logic [63:0] cnt_flush_fencei_fe;
  logic [63:0] cnt_flush_bp_miss;
  logic [63:0] cnt_flush_load_ex;

  always_ff @(posedge clk_i) begin
    cycles_clk_total <= cycles_clk_total + 64'd1;

    if (!rst_ni) begin
      cycles_active           <= '0;
      cycles_stall_total      <= '0;
      cycles_stall_with_flush <= '0;
      cnt_load_raw            <= '0;
      cnt_imiss               <= '0;
      cnt_dmiss               <= '0;
      cnt_alu                 <= '0;
      cnt_fencei              <= '0;
      cnt_l2_miss_cycles      <= '0;
      flush_events_total      <= '0;
      cnt_flush_ex_trap       <= '0;
      cnt_flush_de_trap       <= '0;
      cnt_flush_fencei_fe     <= '0;
      cnt_flush_bp_miss       <= '0;
      cnt_flush_load_ex       <= '0;
    end else begin
      cycles_active <= cycles_active + 64'd1;

      if (stall_cause != NO_STALL) begin
        cycles_stall_total <= cycles_stall_total + 64'd1;
        unique case (stall_cause)
          LOAD_RAW_STALL: cnt_load_raw <= cnt_load_raw + 64'd1;
          IMISS_STALL: cnt_imiss <= cnt_imiss + 64'd1;
          DMISS_STALL: cnt_dmiss <= cnt_dmiss + 64'd1;
          ALU_STALL: cnt_alu <= cnt_alu + 64'd1;
          FENCEI_STALL: cnt_fencei <= cnt_fencei + 64'd1;
          default: ;
        endcase
      end

      if (l2_miss_busy_i) cnt_l2_miss_cycles <= cnt_l2_miss_cycles + 64'd1;

      // One bucket per cycle (exceptions > FENCE.I front flush > BP miss > ex_flush spill)
      if (priority_flush_i == 2'd3) begin
        flush_events_total  <= flush_events_total + 64'd1;
        cnt_flush_ex_trap   <= cnt_flush_ex_trap + 64'd1;
        if (stall_cause != NO_STALL) cycles_stall_with_flush <= cycles_stall_with_flush + 64'd1;
      end else if (priority_flush_i == 2'd2) begin
        flush_events_total  <= flush_events_total + 64'd1;
        cnt_flush_de_trap   <= cnt_flush_de_trap + 64'd1;
        if (stall_cause != NO_STALL) cycles_stall_with_flush <= cycles_stall_with_flush + 64'd1;
      end else if (fencei_flush_i) begin
        flush_events_total  <= flush_events_total + 64'd1;
        cnt_flush_fencei_fe <= cnt_flush_fencei_fe + 64'd1;
        if (stall_cause != NO_STALL) cycles_stall_with_flush <= cycles_stall_with_flush + 64'd1;
      end else if (de_flush_en_i) begin
        flush_events_total <= flush_events_total + 64'd1;
        cnt_flush_bp_miss  <= cnt_flush_bp_miss + 64'd1;
        if (stall_cause != NO_STALL) cycles_stall_with_flush <= cycles_stall_with_flush + 64'd1;
      end else if (ex_flush_en_i) begin
        flush_events_total <= flush_events_total + 64'd1;
        cnt_flush_load_ex  <= cnt_flush_load_ex + 64'd1;
        if (stall_cause != NO_STALL) cycles_stall_with_flush <= cycles_stall_with_flush + 64'd1;
      end
    end
  end

  function automatic int unsigned pct_of(input logic [63:0] tot, input logic [63:0] part);
    if (tot == 64'd0) return 0;
    return int'(part * 64'd100 / tot);
  endfunction

  final begin
    $display("");
    $display("================================================================================");
    $display(" LOG_PERF_STALL — totals, stall cycles, flush events");
    $display(" Stall cause priority: FENCEI > IMISS > DMISS > LOAD_RAW > ALU");
    $display("--------------------------------------------------------------------------------");
    $display("  Clock edges (entire sim, incl. reset):     %0d", cycles_clk_total);
    $display("  Active window (rst high, benchmark payda): %0d", cycles_active);
    $display("--------------------------------------------------------------------------------");
    $display("  SUMMARY (%% of active window, %%s not additive — see overlap line)");
    $display("    Stall cycles:        %0d  (%0d%% of active)", cycles_stall_total,
             pct_of(cycles_active, cycles_stall_total));
    $display("    Cycles w/o stall:    %0d  (%0d%% of active)",
             cycles_active - cycles_stall_total,
             pct_of(cycles_active, cycles_active - cycles_stall_total));
    $display("    Flush events:        %0d  (%0d%% of active cycles had >=1 flush)",
             flush_events_total, pct_of(cycles_active, flush_events_total));
    $display("    Stall same cycle as flush: %0d  (%0d%% of active)",
             cycles_stall_with_flush, pct_of(cycles_active, cycles_stall_with_flush));
    $display(
        "    Flush ~bubble cyc (x2–x3 per event): %0d – %0d  (~%0d%%–%0d%% of active)",
        flush_events_total * 64'd2,
        flush_events_total * 64'd3,
        pct_of(cycles_active, flush_events_total * 64'd2),
        pct_of(cycles_active, flush_events_total * 64'd3));
    $display("--------------------------------------------------------------------------------");
    $display("  Stall breakdown (cycles):");
    $display("    LOAD_RAW_STALL   %0d  load-use / decode hazard", cnt_load_raw);
    $display("    IMISS_STALL      %0d  I-cache miss", cnt_imiss);
    $display("    DMISS_STALL      %0d  D-cache / memory", cnt_dmiss);
    $display("    ALU_STALL        %0d  mul/div", cnt_alu);
    $display("    FENCEI_STALL     %0d  FENCE.I / D$ writeback stall", cnt_fencei);
    $display("    L2 miss cycles   %0d  L2 miss service (l2_miss_busy_o; not in stall buckets)",
             cnt_l2_miss_cycles);
    $display("--------------------------------------------------------------------------------");
    $display("  Flush breakdown (events): EX trap %0d | DE trap %0d | FENCE.I fe %0d | BP miss %0d | ex-only %0d",
             cnt_flush_ex_trap, cnt_flush_de_trap, cnt_flush_fencei_fe, cnt_flush_bp_miss,
             cnt_flush_load_ex);
    $display("================================================================================");
    $display("");
  end

`else
  // LOG_PERF_STALL off: no counters; tie ports for hierarchical consistency.
  wire _unused_perf_ports = ^{
    clk_i,
    rst_ni,
    stall_cause,
    fencei_flush_i,
    priority_flush_i,
    de_flush_en_i,
    ex_flush_en_i,
    l2_miss_busy_i
  };
`endif

endmodule
