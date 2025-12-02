/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  Wishbone B4 Interconnect
  
  Simple 1-to-N crossbar interconnect for Wishbone B4 pipelined bus.
  Decodes address to select appropriate slave.
  
  Slave Map:
    0x8xxx_xxxx : RAM (Main Memory)
    0x3xxx_xxxx : CLINT (Core Local Interruptor)
    0x2xxx_xxxx : PBUS (Peripheral Bus - UART, SPI, I2C, GPIO, etc.)
    
  Features:
  - Address-based slave selection
  - Pipelined operation with stall support
  - Error generation for unmapped addresses
  - Single-cycle decode latency
*/

`timescale 1ns / 1ps
`include "ceres_defines.svh"
import ceres_param::*;

module wb_interconnect #(
    parameter int NUM_SLAVES = 3
) (
    input logic clk_i,
    input logic rst_ni,

    // Wishbone Master interface (from CPU)
    input  wb_master_t wb_m_i,
    output wb_slave_t  wb_s_o,

    // Wishbone Slave interfaces
    output wb_master_t wb_m_o[NUM_SLAVES],
    input  wb_slave_t  wb_s_i[NUM_SLAVES]
);

  // ============================================================================
  // Address Decode
  // ============================================================================
  // Slave selection based on address bits [31:28]
  localparam SLAVE_RAM = 0;
  localparam SLAVE_CLINT = 1;
  localparam SLAVE_PBUS = 2;

  logic [NUM_SLAVES-1:0] slave_sel;
  logic                  addr_valid;
  logic [           1:0] active_slave_q;
  logic                  req_pending_q;

  // Combinational address decode
  always_comb begin
    slave_sel  = '0;
    addr_valid = 1'b0;

    case (wb_m_i.adr[31:28])
      4'h8: begin  // RAM
        slave_sel[SLAVE_RAM] = 1'b1;
        addr_valid = 1'b1;
      end
      4'h3: begin  // CLINT
        slave_sel[SLAVE_CLINT] = 1'b1;
        addr_valid = 1'b1;
      end
      4'h2: begin  // Peripheral Bus
        slave_sel[SLAVE_PBUS] = 1'b1;
        addr_valid = 1'b1;
      end
      default: begin
        addr_valid = 1'b0;
      end
    endcase
  end

  // ============================================================================
  // Request Tracking
  // ============================================================================
  // Track which slave has an outstanding request
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      active_slave_q <= '0;
      req_pending_q  <= 1'b0;
    end else begin
      if (wb_m_i.cyc && wb_m_i.stb && !wb_s_o.stall) begin
        // New request accepted
        for (int i = 0; i < NUM_SLAVES; i++) begin
          if (slave_sel[i]) begin
            active_slave_q <= i[1:0];
`ifdef VERILATOR
            $display("[%0t] WB_INTC: REQ slave=%0d addr=%h we=%b", $time, i, wb_m_i.adr, wb_m_i.we);
`endif
          end
        end
        req_pending_q <= 1'b1;
      end else if (wb_s_o.ack || wb_s_o.err) begin
        // Request completed
`ifdef VERILATOR
        $display("[%0t] WB_INTC: ACK slave=%0d ack=%b err=%b dat=%h", $time, active_slave_q, wb_s_o.ack, wb_s_o.err, wb_s_o.dat);
`endif
        if (wb_m_i.cti == WB_CTI_CLASSIC || wb_m_i.cti == WB_CTI_EOB) begin
          req_pending_q <= 1'b0;
        end
      end
    end
  end

  // ============================================================================
  // Master to Slave Routing
  // ============================================================================
  // Broadcast master signals to all slaves, use select for gating
  always_comb begin
    for (int i = 0; i < NUM_SLAVES; i++) begin
      wb_m_o[i].adr = wb_m_i.adr;
      wb_m_o[i].dat = wb_m_i.dat;
      wb_m_o[i].sel = wb_m_i.sel;
      wb_m_o[i].we  = wb_m_i.we;
      wb_m_o[i].cti = wb_m_i.cti;
      wb_m_o[i].bte = wb_m_i.bte;

      // Gate strobe and cycle with slave select
      wb_m_o[i].stb = wb_m_i.stb && slave_sel[i];
      wb_m_o[i].cyc = wb_m_i.cyc && (slave_sel[i] || (req_pending_q && active_slave_q == i[1:0]));
    end
  end

  // ============================================================================
  // Slave to Master Routing
  // ============================================================================
  // Mux slave responses based on active slave or current selection
  always_comb begin
    // Default: no response
    wb_s_o.dat   = '0;
    wb_s_o.ack   = 1'b0;
    wb_s_o.err   = 1'b0;
    wb_s_o.rty   = 1'b0;
    wb_s_o.stall = 1'b0;

    if (!addr_valid && wb_m_i.cyc && wb_m_i.stb) begin
      // Invalid address - generate error
      wb_s_o.err = 1'b1;
    end else begin
      // Route response from selected slave (use current address decode)
      for (int i = 0; i < NUM_SLAVES; i++) begin
        if (slave_sel[i] || (req_pending_q && active_slave_q == i[1:0])) begin
          wb_s_o.dat   = wb_s_i[i].dat;
          wb_s_o.ack   = wb_s_i[i].ack;
          wb_s_o.err   = wb_s_i[i].err;
          wb_s_o.rty   = wb_s_i[i].rty;
          wb_s_o.stall = wb_s_i[i].stall;
        end
      end
    end
  end

endmodule
