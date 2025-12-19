/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  PLIC (Platform-Level Interrupt Controller)
  
  RISC-V compliant interrupt controller for external interrupts.
  Supports up to 32 interrupt sources with 8 priority levels.
  
  Features:
  - 32 interrupt sources (source 0 is reserved/hardwired to 0)
  - 8 priority levels (0=disabled, 1=lowest, 7=highest)
  - Priority threshold for interrupt masking
  - Claim/Complete mechanism for interrupt handling
  - Edge-triggered interrupt capture
  
  Memory Map (base 0x2000_7000):
    0x000-0x07C : Priority registers (source 1-31, 4 bytes each)
    0x080       : Pending register (32 bits, read-only)
    0x100       : Enable register (32 bits)
    0x200       : Priority threshold
    0x204       : Claim/Complete register
  
  Interrupt Flow:
    1. External source asserts interrupt
    2. If enabled and priority > threshold, PLIC asserts irq_o
    3. CPU reads CLAIM register to get highest priority pending source
    4. Reading CLAIM atomically clears pending bit
    5. CPU handles interrupt
    6. CPU writes source ID to COMPLETE to signal completion
*/
`timescale 1ns / 1ps

module plic
  import ceres_param::*;
#(
    parameter int NUM_SOURCES  = 32,  // Number of interrupt sources (including reserved 0)
    parameter int NUM_PRIORITY = 8    // Number of priority levels (3 bits)
) (
    input logic clk_i,
    input logic rst_ni,

    // Register interface (PBUS style)
    input  logic            stb_i,
    input  logic [     9:0] adr_i,       // 10-bit address for register space
    input  logic [     3:0] byte_sel_i,
    input  logic            we_i,
    input  logic [XLEN-1:0] dat_i,
    output logic [XLEN-1:0] dat_o,

    // Interrupt sources (directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly external)
    input logic [NUM_SOURCES-1:0] irq_sources_i,

    // Interrupt output to CPU
    output logic irq_o
);

  // ============================================================================
  // Local Parameters
  // ============================================================================
  localparam int PRIORITY_BITS = $clog2(NUM_PRIORITY);

  // Register addresses (word aligned)
  localparam logic [9:0] ADDR_PRIORITY_BASE = 10'h000;  // 0x000-0x07C
  localparam logic [9:0] ADDR_PENDING = 10'h080;  // 0x080
  localparam logic [9:0] ADDR_ENABLE = 10'h100;  // 0x100
  localparam logic [9:0] ADDR_THRESHOLD = 10'h200;  // 0x200
  localparam logic [9:0] ADDR_CLAIM = 10'h204;  // 0x204

  // ============================================================================
  // Registers
  // ============================================================================
  logic [PRIORITY_BITS-1:0] priority_q                                 [NUM_SOURCES-1:0];  // Priority per source
  logic [  NUM_SOURCES-1:0] pending_q;  // Pending interrupts
  logic [  NUM_SOURCES-1:0] enable_q;  // Enabled interrupts
  logic [PRIORITY_BITS-1:0] threshold_q;  // Priority threshold
  logic [  NUM_SOURCES-1:0] claimed_q;  // Currently claimed interrupts

  // ============================================================================
  // Edge Detection for Interrupt Sources
  // ============================================================================
  logic [  NUM_SOURCES-1:0] irq_sync1_q;
  logic [  NUM_SOURCES-1:0] irq_sync2_q;
  logic [  NUM_SOURCES-1:0] irq_prev_q;
  logic [  NUM_SOURCES-1:0] irq_edge;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      irq_sync1_q <= '0;
      irq_sync2_q <= '0;
      irq_prev_q  <= '0;
    end else begin
      irq_sync1_q <= irq_sources_i;
      irq_sync2_q <= irq_sync1_q;
      irq_prev_q  <= irq_sync2_q;
    end
  end

  // Rising edge detection
  assign irq_edge = irq_sync2_q & ~irq_prev_q;

  // ============================================================================
  // Find Highest Priority Pending Interrupt
  // ============================================================================
  logic [      PRIORITY_BITS-1:0] max_priority;
  logic [$clog2(NUM_SOURCES)-1:0] max_id;
  logic                           irq_valid;

  always_comb begin
    max_priority = '0;
    max_id = '0;
    irq_valid = 1'b0;

    // Source 0 is reserved, start from 1
    for (int i = 1; i < NUM_SOURCES; i++) begin
      if (pending_q[i] && enable_q[i] && !claimed_q[i]) begin
        if (priority_q[i] > max_priority && priority_q[i] > threshold_q) begin
          max_priority = priority_q[i];
          max_id = i[$clog2(NUM_SOURCES)-1:0];
          irq_valid = 1'b1;
        end
      end
    end
  end

  // Output interrupt to CPU
  assign irq_o = irq_valid;

  // ============================================================================
  // Register Write Logic
  // ============================================================================
  logic reg_write;
  logic claim_read;
  logic complete_write;

  assign reg_write = stb_i && we_i;
  assign claim_read = stb_i && !we_i && (adr_i == ADDR_CLAIM);
  assign complete_write = stb_i && we_i && (adr_i == ADDR_CLAIM);

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      for (int i = 0; i < NUM_SOURCES; i++) begin
        priority_q[i] <= '0;
      end
      pending_q   <= '0;
      enable_q    <= '0;
      threshold_q <= '0;
      claimed_q   <= '0;
    end else begin
      // Capture new interrupts (edge-triggered)
      pending_q <= pending_q | irq_edge;

      // Priority register writes (0x000 - 0x07C, source 1-31)
      /* verilator lint_off UNSIGNED */
      if (reg_write && adr_i >= ADDR_PRIORITY_BASE && adr_i < ADDR_PENDING) begin
      /* verilator lint_on UNSIGNED */
        automatic logic [4:0] src_idx = adr_i[6:2];  // Word index (0-31)
        /* verilator lint_off WIDTHEXPAND */
        if (src_idx > 0 && src_idx < NUM_SOURCES) begin
        /* verilator lint_on WIDTHEXPAND */
          priority_q[src_idx] <= dat_i[PRIORITY_BITS-1:0];
        end
      end

      // Enable register write
      if (reg_write && adr_i == ADDR_ENABLE) begin
        if (byte_sel_i[0]) enable_q[7:0] <= dat_i[7:0];
        if (byte_sel_i[1]) enable_q[15:8] <= dat_i[15:8];
        if (byte_sel_i[2]) enable_q[23:16] <= dat_i[23:16];
        if (byte_sel_i[3]) enable_q[31:24] <= dat_i[31:24];
        // Source 0 is always disabled
        enable_q[0] <= 1'b0;
      end

      // Threshold register write
      if (reg_write && adr_i == ADDR_THRESHOLD) begin
        threshold_q <= dat_i[PRIORITY_BITS-1:0];
      end

      // Claim: reading claim register atomically claims the interrupt
      if (claim_read && irq_valid) begin
        claimed_q[max_id] <= 1'b1;
        pending_q[max_id] <= 1'b0;  // Clear pending when claimed
      end

      // Complete: writing source ID completes the interrupt
      if (complete_write) begin
        automatic logic [$clog2(NUM_SOURCES)-1:0] complete_id = dat_i[$clog2(NUM_SOURCES)-1:0];
        /* verilator lint_off WIDTHEXPAND */
        if (complete_id > 0 && complete_id < NUM_SOURCES) begin
        /* verilator lint_on WIDTHEXPAND */
          claimed_q[complete_id] <= 1'b0;
        end
      end
    end
  end

  // ============================================================================
  // Register Read Logic
  // ============================================================================
  always_comb begin
    dat_o = '0;

    /* verilator lint_off UNSIGNED */
    if (adr_i >= ADDR_PRIORITY_BASE && adr_i < ADDR_PENDING) begin
    /* verilator lint_on UNSIGNED */
      // Priority registers
      automatic logic [4:0] src_idx = adr_i[6:2];
      /* verilator lint_off WIDTHEXPAND */
      if (src_idx < NUM_SOURCES) begin
      /* verilator lint_on WIDTHEXPAND */
        dat_o = {{(32 - PRIORITY_BITS) {1'b0}}, priority_q[src_idx]};
      end
    end else begin
      case (adr_i)
        ADDR_PENDING: begin
          dat_o = pending_q;
        end

        ADDR_ENABLE: begin
          dat_o = enable_q;
        end

        ADDR_THRESHOLD: begin
          dat_o = {{(32 - PRIORITY_BITS) {1'b0}}, threshold_q};
        end

        ADDR_CLAIM: begin
          // Return highest priority pending interrupt ID (or 0 if none)
          dat_o = irq_valid ? {{(32 - $clog2(NUM_SOURCES)) {1'b0}}, max_id} : '0;
        end

        default: begin
          dat_o = '0;
        end
      endcase
    end
  end

  // ============================================================================
  // Assertions (for simulation)
  // ============================================================================
  // synthesis translate_off
  initial begin
    assert (NUM_SOURCES <= 32)
    else $error("NUM_SOURCES must be <= 32");
    assert (NUM_PRIORITY <= 8)
    else $error("NUM_PRIORITY must be <= 8");
  end
  // synthesis translate_on

endmodule
