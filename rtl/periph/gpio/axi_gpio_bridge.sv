/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

================================================================================
AXI-Lite to Simple Bus Bridge for Xilinx GPIO IP
================================================================================
Description:
  This module bridges CERES SoC's simple memory-mapped interface to AXI-Lite,
  allowing connection to Xilinx AXI GPIO IP core.

  Xilinx AXI GPIO IP has the following register map:
    0x00: GPIO_DATA   - Channel 1 Data Register
    0x04: GPIO_TRI    - Channel 1 3-state Control (1=input, 0=output)
    0x08: GPIO2_DATA  - Channel 2 Data Register (if dual channel)
    0x0C: GPIO2_TRI   - Channel 2 3-state Control
    0x11C: GIER       - Global Interrupt Enable Register
    0x128: IP_IER     - IP Interrupt Enable Register
    0x120: IP_ISR     - IP Interrupt Status Register

  This bridge translates the simple bus transactions to AXI-Lite protocol.
================================================================================
*/

`timescale 1ns / 1ps

module axi_gpio_bridge #(
    parameter int C_S_AXI_DATA_WIDTH = 32,
    parameter int C_S_AXI_ADDR_WIDTH = 9    // Xilinx GPIO needs 9-bit address
) (
    // =========================================================================
    // Clock and Reset
    // =========================================================================
    input logic clk_i,
    input logic rst_ni,

    // =========================================================================
    // Simple Bus Interface (from CERES SoC)
    // =========================================================================
    input  logic                          stb_i,       // Strobe/valid
    input  logic [C_S_AXI_ADDR_WIDTH-3:0] adr_i,       // Word address
    input  logic [                   3:0] byte_sel_i,  // Byte enables
    input  logic                          we_i,        // Write enable
    input  logic [                  31:0] dat_i,       // Write data
    output logic [                  31:0] dat_o,       // Read data
    output logic                          ack_o,       // Acknowledge

    // =========================================================================
    // AXI-Lite Master Interface (to Xilinx GPIO IP)
    // =========================================================================
    // Write Address Channel
    output logic [C_S_AXI_ADDR_WIDTH-1:0] m_axi_awaddr,
    output logic [                   2:0] m_axi_awprot,
    output logic                          m_axi_awvalid,
    input  logic                          m_axi_awready,

    // Write Data Channel
    output logic [  C_S_AXI_DATA_WIDTH-1:0] m_axi_wdata,
    output logic [C_S_AXI_DATA_WIDTH/8-1:0] m_axi_wstrb,
    output logic                            m_axi_wvalid,
    input  logic                            m_axi_wready,

    // Write Response Channel
    input  logic [1:0] m_axi_bresp,
    input  logic       m_axi_bvalid,
    output logic       m_axi_bready,

    // Read Address Channel
    output logic [C_S_AXI_ADDR_WIDTH-1:0] m_axi_araddr,
    output logic [                   2:0] m_axi_arprot,
    output logic                          m_axi_arvalid,
    input  logic                          m_axi_arready,

    // Read Data Channel
    input  logic [C_S_AXI_DATA_WIDTH-1:0] m_axi_rdata,
    input  logic [                   1:0] m_axi_rresp,
    input  logic                          m_axi_rvalid,
    output logic                          m_axi_rready
);

  // ===========================================================================
  // State Machine
  // ===========================================================================
  typedef enum logic [2:0] {
    ST_IDLE,
    ST_WRITE_ADDR,
    ST_WRITE_DATA,
    ST_WRITE_RESP,
    ST_READ_ADDR,
    ST_READ_DATA
  } state_t;

  state_t state_q, state_d;

  // ===========================================================================
  // Internal Signals
  // ===========================================================================
  logic [31:0] rdata_q;
  logic        is_write;

  assign is_write = we_i;

  // Convert word address to byte address
  wire [C_S_AXI_ADDR_WIDTH-1:0] byte_addr = {adr_i, 2'b00};

  // ===========================================================================
  // State Machine Logic
  // ===========================================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= ST_IDLE;
      rdata_q <= 32'h0;
    end else begin
      state_q <= state_d;

      if (state_q == ST_READ_DATA && m_axi_rvalid) begin
        rdata_q <= m_axi_rdata;
      end
    end
  end

  always_comb begin
    state_d = state_q;

    case (state_q)
      ST_IDLE: begin
        if (stb_i) begin
          if (is_write) begin
            state_d = ST_WRITE_ADDR;
          end else begin
            state_d = ST_READ_ADDR;
          end
        end
      end

      ST_WRITE_ADDR: begin
        if (m_axi_awready) begin
          state_d = ST_WRITE_DATA;
        end
      end

      ST_WRITE_DATA: begin
        if (m_axi_wready) begin
          state_d = ST_WRITE_RESP;
        end
      end

      ST_WRITE_RESP: begin
        if (m_axi_bvalid) begin
          state_d = ST_IDLE;
        end
      end

      ST_READ_ADDR: begin
        if (m_axi_arready) begin
          state_d = ST_READ_DATA;
        end
      end

      ST_READ_DATA: begin
        if (m_axi_rvalid) begin
          state_d = ST_IDLE;
        end
      end

      default: state_d = ST_IDLE;
    endcase
  end

  // ===========================================================================
  // AXI-Lite Output Signals
  // ===========================================================================

  // Write Address Channel
  assign m_axi_awaddr = byte_addr;
  assign m_axi_awprot = 3'b000;  // Unprivileged, secure, data
  assign m_axi_awvalid = (state_q == ST_WRITE_ADDR);

  // Write Data Channel
  assign m_axi_wdata = dat_i;
  assign m_axi_wstrb = byte_sel_i;
  assign m_axi_wvalid = (state_q == ST_WRITE_DATA);

  // Write Response Channel
  assign m_axi_bready = (state_q == ST_WRITE_RESP);

  // Read Address Channel
  assign m_axi_araddr = byte_addr;
  assign m_axi_arprot = 3'b000;
  assign m_axi_arvalid = (state_q == ST_READ_ADDR);

  // Read Data Channel
  assign m_axi_rready = (state_q == ST_READ_DATA);

  // ===========================================================================
  // Simple Bus Output Signals
  // ===========================================================================
  assign dat_o = rdata_q;
  assign ack_o = (state_q == ST_WRITE_RESP && m_axi_bvalid) || (state_q == ST_READ_DATA && m_axi_rvalid);

endmodule
