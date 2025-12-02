/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  Wishbone B4 RAM Slave
  
  Simple synchronous RAM with Wishbone B4 pipelined interface.
  Supports single and burst transfers.
  
  Features:
  - Configurable depth and latency
  - Burst support for cache line fills
  - Byte-enable writes
  - Single-cycle read/write for zero-wait states
*/

`timescale 1ns / 1ps
`include "ceres_defines.svh"
import ceres_param::*;

module wb_ram_slave #(
    parameter int RAM_DEPTH   = 32768,  // Number of 32-bit words
    parameter int RAM_LATENCY = 1       // Read latency cycles
) (
    input logic clk_i,
    input logic rst_ni,

    // Wishbone Slave interface
    input  wb_master_t wb_m_i,
    output wb_slave_t  wb_s_o,

    // RAM interface (directly connected to BRAM)
    output logic [31:0] ram_addr_o,
    output logic [31:0] ram_wdata_o,
    output logic [ 3:0] ram_wstrb_o,
    output logic        ram_rd_en_o,
    input  logic [31:0] ram_rdata_i
);

  // ============================================================================
  // Local Parameters
  // ============================================================================
  localparam ADDR_WIDTH = $clog2(RAM_DEPTH);

  // ============================================================================
  // Latency Pipeline
  // ============================================================================
  logic [RAM_LATENCY:0] valid_pipe;
  logic                 we_q;

  // ============================================================================
  // Request Handling
  // ============================================================================
  logic                 req_valid;
  logic                 req_we;
  logic [         31:0] req_addr;

  assign req_valid = wb_m_i.cyc && wb_m_i.stb;
  assign req_we    = wb_m_i.we;
  assign req_addr  = wb_m_i.adr;

  // ============================================================================
  // RAM Interface
  // ============================================================================
  // Convert Wishbone address to word address
  assign ram_addr_o  = {2'b00, req_addr[ADDR_WIDTH+1:2]};  // Word-aligned
  assign ram_wdata_o = wb_m_i.dat;
  assign ram_wstrb_o = req_valid && req_we ? wb_m_i.sel : 4'b0;
  assign ram_rd_en_o = req_valid && !req_we;

  // ============================================================================
  // Latency Pipeline for Reads
  // ============================================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_pipe <= '0;
      we_q       <= 1'b0;
    end else begin
      // Shift valid through pipeline
      valid_pipe[0] <= req_valid;
      for (int i = 1; i <= RAM_LATENCY; i++) begin
        valid_pipe[i] <= valid_pipe[i-1];
      end
      we_q <= req_we;
    end
  end

  // ============================================================================
  // Wishbone Response
  // ============================================================================
  // For writes: immediate ack
  // For reads: ack after latency pipeline
  assign wb_s_o.dat   = ram_rdata_i;
  assign wb_s_o.ack   = (req_valid && req_we) || (valid_pipe[RAM_LATENCY] && !we_q);
  assign wb_s_o.err   = 1'b0;
  assign wb_s_o.rty   = 1'b0;
  assign wb_s_o.stall = 1'b0;  // No stall - always ready

endmodule
