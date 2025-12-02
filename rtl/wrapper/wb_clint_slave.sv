/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  Wishbone B4 CLINT Slave
  
  Core Local Interruptor with Wishbone B4 interface.
  Implements RISC-V CLINT specification.
  
  Register Map (base 0x3000_0000):
    0x0000 : MSIP (Machine Software Interrupt Pending)
    0x4000 : MTIMECMP_LO (Machine Timer Compare - Low 32 bits)
    0x4004 : MTIMECMP_HI (Machine Timer Compare - High 32 bits)
    0xBFF8 : MTIME_LO (Machine Time - Low 32 bits)
    0xBFFC : MTIME_HI (Machine Time - High 32 bits)
    
  Features:
  - 64-bit mtime counter
  - 64-bit mtimecmp register
  - msip software interrupt register
  - Timer interrupt generation
*/

`timescale 1ns / 1ps
`include "ceres_defines.svh"
import ceres_param::*;

module wb_clint_slave (
    input logic clk_i,
    input logic rst_ni,

    // Wishbone Slave interface
    input  wb_master_t wb_m_i,
    output wb_slave_t  wb_s_o,

    // Interrupt outputs
    output logic timer_irq_o,
    output logic sw_irq_o
);

  // ============================================================================
  // CLINT Register Offsets
  // ============================================================================
  localparam CLINT_MSIP = 16'h0000;
  localparam CLINT_MTIMECMP_LO = 16'h4000;
  localparam CLINT_MTIMECMP_HI = 16'h4004;
  localparam CLINT_MTIME_LO = 16'hBFF8;
  localparam CLINT_MTIME_HI = 16'hBFFC;

  // ============================================================================
  // Registers
  // ============================================================================
  logic [63:0] mtime_q;
  logic [63:0] mtimecmp_q;
  logic        msip_q;

  // ============================================================================
  // Request Handling
  // ============================================================================
  logic        req_valid;
  logic        req_we;
  logic [15:0] reg_offset;

  assign req_valid   = wb_m_i.cyc && wb_m_i.stb;
  assign req_we      = wb_m_i.we;
  assign reg_offset  = wb_m_i.adr[15:0];

  // ============================================================================
  // Timer Interrupt
  // ============================================================================
  assign timer_irq_o = (mtime_q >= mtimecmp_q);
  assign sw_irq_o    = msip_q;

  // ============================================================================
  // Register Read
  // ============================================================================
  logic [31:0] rdata;

  always_comb begin
    rdata = 32'h0;
    case (reg_offset)
      CLINT_MSIP:        rdata = {31'b0, msip_q};
      CLINT_MTIMECMP_LO: rdata = mtimecmp_q[31:0];
      CLINT_MTIMECMP_HI: rdata = mtimecmp_q[63:32];
      CLINT_MTIME_LO:    rdata = mtime_q[31:0];
      CLINT_MTIME_HI:    rdata = mtime_q[63:32];
      default:           rdata = 32'h0;
    endcase
  end

  // ============================================================================
  // Register Write
  // ============================================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      mtime_q    <= 64'h0;
      mtimecmp_q <= 64'hFFFF_FFFF_FFFF_FFFF;  // Max value to prevent spurious interrupts
      msip_q     <= 1'b0;
    end else begin
      // Timer always increments
      mtime_q <= mtime_q + 1;

      // Register writes
      if (req_valid && req_we) begin
        case (reg_offset)
          CLINT_MSIP:        msip_q <= wb_m_i.dat[0];
          CLINT_MTIMECMP_LO: mtimecmp_q[31:0] <= wb_m_i.dat;
          CLINT_MTIMECMP_HI: mtimecmp_q[63:32] <= wb_m_i.dat;
          CLINT_MTIME_LO:    mtime_q[31:0] <= wb_m_i.dat;
          CLINT_MTIME_HI:    mtime_q[63:32] <= wb_m_i.dat;
          default:           ;
        endcase
      end
    end
  end

  // ============================================================================
  // Wishbone Response
  // ============================================================================
  assign wb_s_o.dat   = rdata;
  assign wb_s_o.ack   = req_valid;  // Single-cycle response
  assign wb_s_o.err   = 1'b0;
  assign wb_s_o.rty   = 1'b0;
  assign wb_s_o.stall = 1'b0;

endmodule
