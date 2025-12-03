/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

================================================================================
Xilinx AXI GPIO Wrapper for CERES SoC
================================================================================
Description:
  This module wraps Xilinx AXI GPIO IP for direct integration with CERES SoC.
  It instantiates the AXI-Lite bridge and connects to Xilinx GPIO IP.

  For Vivado:
    1. Add this file to your project
    2. Create a Block Design with AXI GPIO IP
    3. Set GPIO IP to "All Outputs" or "All Inputs" or "Dual Channel" as needed
    4. Connect the AXI interface signals

  Xilinx GPIO Configuration Options:
    - GPIO Width: 1-32 bits per channel
    - Dual Channel: Enable for two GPIO banks
    - All Inputs/All Outputs: Simplify if direction is fixed
    - Default Value: Initial output value
    - Tri Default: Initial tri-state value (1=input)
    - Interrupt: Enable interrupt on change

Usage in CERES SoC:
  Set GPIO_EN = 1'b0 (disable internal GPIO)
  Set XILINX_GPIO_EN = 1'b1 (enable this wrapper)
================================================================================
*/

`timescale 1ns / 1ps

module xilinx_gpio_wrapper #(
    parameter int GPIO_WIDTH   = 32,
    parameter bit DUAL_CHANNEL = 1'b0,
    parameter bit INTERRUPT_EN = 1'b1
) (
    // =========================================================================
    // Clock and Reset
    // =========================================================================
    input logic clk_i,
    input logic rst_ni,

    // =========================================================================
    // Simple Bus Interface (from CERES SoC peripheral mux)
    // =========================================================================
    input  logic        stb_i,
    input  logic [ 6:0] adr_i,       // Word address [8:2]
    input  logic [ 3:0] byte_sel_i,
    input  logic        we_i,
    input  logic [31:0] dat_i,
    output logic [31:0] dat_o,
    output logic        ack_o,

    // =========================================================================
    // GPIO Channel 1
    // =========================================================================
    input  logic [GPIO_WIDTH-1:0] gpio_i,
    output logic [GPIO_WIDTH-1:0] gpio_o,
    output logic [GPIO_WIDTH-1:0] gpio_t,  // Active-high tri-state (1=input)

    // =========================================================================
    // GPIO Channel 2 (if DUAL_CHANNEL)
    // =========================================================================
    input  logic [GPIO_WIDTH-1:0] gpio2_i,
    output logic [GPIO_WIDTH-1:0] gpio2_o,
    output logic [GPIO_WIDTH-1:0] gpio2_t,

    // =========================================================================
    // Interrupt Output
    // =========================================================================
    output logic irq_o
);

  // ===========================================================================
  // AXI-Lite Signals
  // ===========================================================================
  logic [ 8:0] m_axi_awaddr;
  logic [ 2:0] m_axi_awprot;
  logic        m_axi_awvalid;
  logic        m_axi_awready;
  logic [31:0] m_axi_wdata;
  logic [ 3:0] m_axi_wstrb;
  logic        m_axi_wvalid;
  logic        m_axi_wready;
  logic [ 1:0] m_axi_bresp;
  logic        m_axi_bvalid;
  logic        m_axi_bready;
  logic [ 8:0] m_axi_araddr;
  logic [ 2:0] m_axi_arprot;
  logic        m_axi_arvalid;
  logic        m_axi_arready;
  logic [31:0] m_axi_rdata;
  logic [ 1:0] m_axi_rresp;
  logic        m_axi_rvalid;
  logic        m_axi_rready;

  // ===========================================================================
  // AXI-Lite Bridge
  // ===========================================================================
  axi_gpio_bridge #(
      .C_S_AXI_DATA_WIDTH(32),
      .C_S_AXI_ADDR_WIDTH(9)
  ) u_bridge (
      .clk_i        (clk_i),
      .rst_ni       (rst_ni),
      // Simple bus
      .stb_i        (stb_i),
      .adr_i        (adr_i),
      .byte_sel_i   (byte_sel_i),
      .we_i         (we_i),
      .dat_i        (dat_i),
      .dat_o        (dat_o),
      .ack_o        (ack_o),
      // AXI-Lite Master
      .m_axi_awaddr (m_axi_awaddr),
      .m_axi_awprot (m_axi_awprot),
      .m_axi_awvalid(m_axi_awvalid),
      .m_axi_awready(m_axi_awready),
      .m_axi_wdata  (m_axi_wdata),
      .m_axi_wstrb  (m_axi_wstrb),
      .m_axi_wvalid (m_axi_wvalid),
      .m_axi_wready (m_axi_wready),
      .m_axi_bresp  (m_axi_bresp),
      .m_axi_bvalid (m_axi_bvalid),
      .m_axi_bready (m_axi_bready),
      .m_axi_araddr (m_axi_araddr),
      .m_axi_arprot (m_axi_arprot),
      .m_axi_arvalid(m_axi_arvalid),
      .m_axi_arready(m_axi_arready),
      .m_axi_rdata  (m_axi_rdata),
      .m_axi_rresp  (m_axi_rresp),
      .m_axi_rvalid (m_axi_rvalid),
      .m_axi_rready (m_axi_rready)
  );

  // ===========================================================================
  // Xilinx AXI GPIO IP Instance
  // ===========================================================================
  // This is a black-box instantiation - Vivado will elaborate the actual IP
  //
  // In Vivado Block Design:
  //   1. Add IP -> AXI GPIO
  //   2. Configure: GPIO Width, Dual Channel, Interrupt, etc.
  //   3. Right-click -> Create HDL Wrapper
  //   4. Or use this direct instantiation with matching parameters

  /* verilator lint_off DECLFILENAME */
  axi_gpio_0 u_axi_gpio (
      // AXI-Lite Slave Interface
      .s_axi_aclk   (clk_i),
      .s_axi_aresetn(rst_ni),
      .s_axi_awaddr (m_axi_awaddr),
      .s_axi_awvalid(m_axi_awvalid),
      .s_axi_awready(m_axi_awready),
      .s_axi_wdata  (m_axi_wdata),
      .s_axi_wstrb  (m_axi_wstrb),
      .s_axi_wvalid (m_axi_wvalid),
      .s_axi_wready (m_axi_wready),
      .s_axi_bresp  (m_axi_bresp),
      .s_axi_bvalid (m_axi_bvalid),
      .s_axi_bready (m_axi_bready),
      .s_axi_araddr (m_axi_araddr),
      .s_axi_arvalid(m_axi_arvalid),
      .s_axi_arready(m_axi_arready),
      .s_axi_rdata  (m_axi_rdata),
      .s_axi_rresp  (m_axi_rresp),
      .s_axi_rvalid (m_axi_rvalid),
      .s_axi_rready (m_axi_rready),
      // GPIO Channel 1
      .gpio_io_i    (gpio_i),
      .gpio_io_o    (gpio_o),
      .gpio_io_t    (gpio_t),
      // GPIO Channel 2 (optional)
      .gpio2_io_i   (gpio2_i),
      .gpio2_io_o   (gpio2_o),
      .gpio2_io_t   (gpio2_t),
      // Interrupt
      .ip2intc_irpt (irq_o)
  );
  /* verilator lint_on DECLFILENAME */

endmodule


// =============================================================================
// Vivado Tcl Script to Create AXI GPIO IP
// =============================================================================
// Save the following as create_axi_gpio.tcl and source in Vivado:
/*

# Create AXI GPIO IP
create_ip -name axi_gpio -vendor xilinx.com -library ip -version 2.0 -module_name axi_gpio_0

# Configure IP
set_property -dict [list \
  CONFIG.C_GPIO_WIDTH {32} \
  CONFIG.C_GPIO2_WIDTH {32} \
  CONFIG.C_IS_DUAL {0} \
  CONFIG.C_ALL_INPUTS {0} \
  CONFIG.C_ALL_OUTPUTS {0} \
  CONFIG.C_ALL_INPUTS_2 {0} \
  CONFIG.C_ALL_OUTPUTS_2 {0} \
  CONFIG.C_INTERRUPT_PRESENT {1} \
  CONFIG.C_DOUT_DEFAULT {0x00000000} \
  CONFIG.C_TRI_DEFAULT {0xFFFFFFFF} \
] [get_ips axi_gpio_0]

# Generate output products
generate_target all [get_files axi_gpio_0.xci]

*/
