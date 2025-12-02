/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  Wishbone B4 Peripheral Bus Slave
  
  Wishbone slave interface for peripheral bus.
  Provides simple register-style access to peripherals.
  
  Address Decode (within 0x2000_xxxx):
    0x2000_0xxx : UART0
    0x2000_1xxx : UART1 (reserved)
    0x2000_2xxx : SPI0 (reserved)
    0x2000_3xxx : I2C0 (reserved)
    0x2000_4xxx : GPIO (reserved)
    0x2000_5xxx : PWM (reserved)
    0x2000_6xxx : Timer (reserved)
    0x2000_7xxx : PLIC (reserved)
    
  Features:
  - Single-cycle access for register reads/writes
  - No burst support (peripherals are uncached)
  - Directly exposes signals for peripheral connection
*/

`timescale 1ns / 1ps
`include "ceres_defines.svh"
import ceres_param::*;

module wb_pbus_slave (
    input logic clk_i,
    input logic rst_ni,

    // Wishbone Slave interface
    input  wb_master_t wb_m_i,
    output wb_slave_t  wb_s_o,

    // Peripheral interface (directly to peripherals)
    output logic [31:0] pbus_addr_o,
    output logic [31:0] pbus_wdata_o,
    output logic [ 3:0] pbus_wstrb_o,
    output logic        pbus_valid_o,
    output logic        pbus_we_o,
    input  logic [31:0] pbus_rdata_i,
    input  logic        pbus_ready_i
);

  // ============================================================================
  // Request Handling
  // ============================================================================
  logic req_valid;
  logic req_we;

  assign req_valid = wb_m_i.cyc && wb_m_i.stb;
  assign req_we    = wb_m_i.we;

  // ============================================================================
  // Peripheral Interface
  // ============================================================================
  assign pbus_addr_o  = wb_m_i.adr;
  assign pbus_wdata_o = wb_m_i.dat;
  assign pbus_wstrb_o = req_valid && req_we ? wb_m_i.sel : 4'b0;
  assign pbus_valid_o = req_valid;
  assign pbus_we_o    = req_we;

  // ============================================================================
  // Wishbone Response
  // ============================================================================
  assign wb_s_o.dat   = pbus_rdata_i;
  assign wb_s_o.ack   = req_valid && pbus_ready_i;
  assign wb_s_o.err   = 1'b0;
  assign wb_s_o.rty   = 1'b0;
  assign wb_s_o.stall = req_valid && !pbus_ready_i;

endmodule
