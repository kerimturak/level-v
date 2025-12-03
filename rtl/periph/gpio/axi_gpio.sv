/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

================================================================================
AXI-Lite GPIO Controller (Xilinx Compatible)
================================================================================
Description:
  Drop-in replacement for Xilinx AXI GPIO IP with identical register map.
  Can be used standalone or mixed with Xilinx IPs in Block Design.

  Register Map (Xilinx AXI GPIO Compatible):
    0x000: GPIO_DATA    - Channel 1 Data Register
    0x004: GPIO_TRI     - Channel 1 Tri-state Control (1=input, 0=output)
    0x008: GPIO2_DATA   - Channel 2 Data Register
    0x00C: GPIO2_TRI    - Channel 2 Tri-state Control
    0x11C: GIER         - Global Interrupt Enable Register [31]
    0x120: IP_ISR       - IP Interrupt Status Register [0]=Ch1, [1]=Ch2
    0x128: IP_IER       - IP Interrupt Enable Register [0]=Ch1, [1]=Ch2

  Features:
    - 100% Xilinx AXI GPIO register-compatible
    - Configurable GPIO width (1-32 bits)
    - Optional dual channel
    - Interrupt on change detection
    - Standard AXI-Lite slave interface
================================================================================
*/

`timescale 1ns / 1ps

module axi_gpio #(
    // GPIO Configuration
    parameter int          C_GPIO_WIDTH        = 32,
    parameter int          C_GPIO2_WIDTH       = 32,
    parameter bit          C_IS_DUAL           = 1'b0,
    parameter bit          C_ALL_INPUTS        = 1'b0,           // Channel 1 all inputs
    parameter bit          C_ALL_OUTPUTS       = 1'b0,           // Channel 1 all outputs
    parameter bit          C_ALL_INPUTS_2      = 1'b0,           // Channel 2 all inputs
    parameter bit          C_ALL_OUTPUTS_2     = 1'b0,           // Channel 2 all outputs
    parameter bit          C_INTERRUPT_PRESENT = 1'b1,
    parameter logic [31:0] C_DOUT_DEFAULT      = 32'h0000_0000,
    parameter logic [31:0] C_TRI_DEFAULT       = 32'hFFFF_FFFF,
    parameter logic [31:0] C_DOUT_DEFAULT_2    = 32'h0000_0000,
    parameter logic [31:0] C_TRI_DEFAULT_2     = 32'hFFFF_FFFF,
    // AXI Parameters
    parameter int          C_S_AXI_ADDR_WIDTH  = 9,
    parameter int          C_S_AXI_DATA_WIDTH  = 32
) (
    // =========================================================================
    // AXI-Lite Slave Interface
    // =========================================================================
    input  logic                            s_axi_aclk,
    input  logic                            s_axi_aresetn,
    // Write Address
    input  logic [  C_S_AXI_ADDR_WIDTH-1:0] s_axi_awaddr,
    input  logic                            s_axi_awvalid,
    output logic                            s_axi_awready,
    // Write Data
    input  logic [  C_S_AXI_DATA_WIDTH-1:0] s_axi_wdata,
    input  logic [C_S_AXI_DATA_WIDTH/8-1:0] s_axi_wstrb,
    input  logic                            s_axi_wvalid,
    output logic                            s_axi_wready,
    // Write Response
    output logic [                     1:0] s_axi_bresp,
    output logic                            s_axi_bvalid,
    input  logic                            s_axi_bready,
    // Read Address
    input  logic [  C_S_AXI_ADDR_WIDTH-1:0] s_axi_araddr,
    input  logic                            s_axi_arvalid,
    output logic                            s_axi_arready,
    // Read Data
    output logic [  C_S_AXI_DATA_WIDTH-1:0] s_axi_rdata,
    output logic [                     1:0] s_axi_rresp,
    output logic                            s_axi_rvalid,
    input  logic                            s_axi_rready,

    // =========================================================================
    // GPIO Channel 1
    // =========================================================================
    input  logic [C_GPIO_WIDTH-1:0] gpio_io_i,
    output logic [C_GPIO_WIDTH-1:0] gpio_io_o,
    output logic [C_GPIO_WIDTH-1:0] gpio_io_t,  // Tri-state (1=input)

    // =========================================================================
    // GPIO Channel 2 (optional)
    // =========================================================================
    input  logic [C_GPIO2_WIDTH-1:0] gpio2_io_i,
    output logic [C_GPIO2_WIDTH-1:0] gpio2_io_o,
    output logic [C_GPIO2_WIDTH-1:0] gpio2_io_t,

    // =========================================================================
    // Interrupt
    // =========================================================================
    output logic ip2intc_irpt
);

  // ===========================================================================
  // Register Addresses (Xilinx Compatible)
  // ===========================================================================
  localparam logic [8:0] ADDR_GPIO_DATA = 9'h000;
  localparam logic [8:0] ADDR_GPIO_TRI = 9'h004;
  localparam logic [8:0] ADDR_GPIO2_DATA = 9'h008;
  localparam logic [8:0] ADDR_GPIO2_TRI = 9'h00C;
  localparam logic [8:0] ADDR_GIER = 9'h11C;
  localparam logic [8:0] ADDR_IP_ISR = 9'h120;
  localparam logic [8:0] ADDR_IP_IER = 9'h128;

  // ===========================================================================
  // Internal Registers
  // ===========================================================================
  logic [             31:0] gpio_data_q;
  logic [             31:0] gpio_tri_q;
  logic [             31:0] gpio2_data_q;
  logic [             31:0] gpio2_tri_q;
  logic                     gier_q;  // Global interrupt enable (bit 31)
  logic [              1:0] ip_ier_q;  // Interrupt enable: [0]=ch1, [1]=ch2
  logic [              1:0] ip_isr_q;  // Interrupt status: [0]=ch1, [1]=ch2

  // Previous input values for edge detection
  logic [ C_GPIO_WIDTH-1:0] gpio_prev_q;
  logic [C_GPIO2_WIDTH-1:0] gpio2_prev_q;

  // Synchronized inputs
  logic [ C_GPIO_WIDTH-1:0] gpio_sync_q;
  logic [ C_GPIO_WIDTH-1:0] gpio_sync_qq;
  logic [C_GPIO2_WIDTH-1:0] gpio2_sync_q;
  logic [C_GPIO2_WIDTH-1:0] gpio2_sync_qq;

  // ===========================================================================
  // AXI-Lite State Machine
  // ===========================================================================
  typedef enum logic [1:0] {
    AXI_IDLE,
    AXI_WRITE,
    AXI_READ
  } axi_state_t;

  axi_state_t        state_q;
  logic       [ 8:0] axi_addr_q;
  logic       [31:0] axi_wdata_q;
  logic       [ 3:0] axi_wstrb_q;

  // ===========================================================================
  // Input Synchronizer (2-stage)
  // ===========================================================================
  always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
    if (!s_axi_aresetn) begin
      gpio_sync_q   <= '0;
      gpio_sync_qq  <= '0;
      gpio2_sync_q  <= '0;
      gpio2_sync_qq <= '0;
      gpio_prev_q   <= '0;
      gpio2_prev_q  <= '0;
    end else begin
      gpio_sync_q   <= gpio_io_i;
      gpio_sync_qq  <= gpio_sync_q;
      gpio2_sync_q  <= gpio2_io_i;
      gpio2_sync_qq <= gpio2_sync_q;
      gpio_prev_q   <= gpio_sync_qq;
      gpio2_prev_q  <= gpio2_sync_qq;
    end
  end

  // ===========================================================================
  // Interrupt Detection
  // ===========================================================================
  wire gpio_changed = |(gpio_sync_qq ^ gpio_prev_q);
  wire gpio2_changed = |(gpio2_sync_qq ^ gpio2_prev_q);

  always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
    if (!s_axi_aresetn) begin
      ip_isr_q <= 2'b00;
    end else begin
      // Set on change
      if (gpio_changed) ip_isr_q[0] <= 1'b1;
      if (gpio2_changed) ip_isr_q[1] <= 1'b1;

      // Clear on write (Toggle-on-Write)
      if (state_q == AXI_WRITE && axi_addr_q == ADDR_IP_ISR) begin
        if (axi_wstrb_q[0] && axi_wdata_q[0]) ip_isr_q[0] <= 1'b0;
        if (axi_wstrb_q[0] && axi_wdata_q[1]) ip_isr_q[1] <= 1'b0;
      end
    end
  end

  // Interrupt output
  assign ip2intc_irpt = C_INTERRUPT_PRESENT ? (gier_q & ((ip_isr_q[0] & ip_ier_q[0]) | (ip_isr_q[1] & ip_ier_q[1]))) : 1'b0;

  // ===========================================================================
  // AXI-Lite FSM
  // ===========================================================================
  always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
    if (!s_axi_aresetn) begin
      state_q     <= AXI_IDLE;
      axi_addr_q  <= '0;
      axi_wdata_q <= '0;
      axi_wstrb_q <= '0;
    end else begin
      case (state_q)
        AXI_IDLE: begin
          if (s_axi_awvalid && s_axi_wvalid) begin
            state_q     <= AXI_WRITE;
            axi_addr_q  <= s_axi_awaddr;
            axi_wdata_q <= s_axi_wdata;
            axi_wstrb_q <= s_axi_wstrb;
          end else if (s_axi_arvalid) begin
            state_q    <= AXI_READ;
            axi_addr_q <= s_axi_araddr;
          end
        end

        AXI_WRITE: begin
          if (s_axi_bready) begin
            state_q <= AXI_IDLE;
          end
        end

        AXI_READ: begin
          if (s_axi_rready) begin
            state_q <= AXI_IDLE;
          end
        end

        default: state_q <= AXI_IDLE;
      endcase
    end
  end

  // ===========================================================================
  // Register Write Logic
  // ===========================================================================
  always_ff @(posedge s_axi_aclk or negedge s_axi_aresetn) begin
    if (!s_axi_aresetn) begin
      gpio_data_q  <= C_DOUT_DEFAULT;
      gpio_tri_q   <= C_ALL_OUTPUTS ? 32'h0 : (C_ALL_INPUTS ? 32'hFFFFFFFF : C_TRI_DEFAULT);
      gpio2_data_q <= C_DOUT_DEFAULT_2;
      gpio2_tri_q  <= C_ALL_OUTPUTS_2 ? 32'h0 : (C_ALL_INPUTS_2 ? 32'hFFFFFFFF : C_TRI_DEFAULT_2);
      gier_q       <= 1'b0;
      ip_ier_q     <= 2'b00;
    end else if (state_q == AXI_WRITE) begin
      case (axi_addr_q)
        ADDR_GPIO_DATA: begin
          if (axi_wstrb_q[0]) gpio_data_q[7:0] <= axi_wdata_q[7:0];
          if (axi_wstrb_q[1]) gpio_data_q[15:8] <= axi_wdata_q[15:8];
          if (axi_wstrb_q[2]) gpio_data_q[23:16] <= axi_wdata_q[23:16];
          if (axi_wstrb_q[3]) gpio_data_q[31:24] <= axi_wdata_q[31:24];
        end

        ADDR_GPIO_TRI: begin
          if (!C_ALL_INPUTS && !C_ALL_OUTPUTS) begin
            if (axi_wstrb_q[0]) gpio_tri_q[7:0] <= axi_wdata_q[7:0];
            if (axi_wstrb_q[1]) gpio_tri_q[15:8] <= axi_wdata_q[15:8];
            if (axi_wstrb_q[2]) gpio_tri_q[23:16] <= axi_wdata_q[23:16];
            if (axi_wstrb_q[3]) gpio_tri_q[31:24] <= axi_wdata_q[31:24];
          end
        end

        ADDR_GPIO2_DATA: begin
          if (C_IS_DUAL) begin
            if (axi_wstrb_q[0]) gpio2_data_q[7:0] <= axi_wdata_q[7:0];
            if (axi_wstrb_q[1]) gpio2_data_q[15:8] <= axi_wdata_q[15:8];
            if (axi_wstrb_q[2]) gpio2_data_q[23:16] <= axi_wdata_q[23:16];
            if (axi_wstrb_q[3]) gpio2_data_q[31:24] <= axi_wdata_q[31:24];
          end
        end

        ADDR_GPIO2_TRI: begin
          if (C_IS_DUAL && !C_ALL_INPUTS_2 && !C_ALL_OUTPUTS_2) begin
            if (axi_wstrb_q[0]) gpio2_tri_q[7:0] <= axi_wdata_q[7:0];
            if (axi_wstrb_q[1]) gpio2_tri_q[15:8] <= axi_wdata_q[15:8];
            if (axi_wstrb_q[2]) gpio2_tri_q[23:16] <= axi_wdata_q[23:16];
            if (axi_wstrb_q[3]) gpio2_tri_q[31:24] <= axi_wdata_q[31:24];
          end
        end

        ADDR_GIER: begin
          if (C_INTERRUPT_PRESENT && axi_wstrb_q[3]) begin
            gier_q <= axi_wdata_q[31];
          end
        end

        ADDR_IP_IER: begin
          if (C_INTERRUPT_PRESENT && axi_wstrb_q[0]) begin
            ip_ier_q <= axi_wdata_q[1:0];
          end
        end

        default: ;
      endcase
    end
  end

  // ===========================================================================
  // Register Read Logic
  // ===========================================================================
  always_comb begin
    s_axi_rdata = 32'h0;
    case (axi_addr_q)
      ADDR_GPIO_DATA:  s_axi_rdata = gpio_sync_qq;
      ADDR_GPIO_TRI:   s_axi_rdata = gpio_tri_q;
      ADDR_GPIO2_DATA: s_axi_rdata = C_IS_DUAL ? gpio2_sync_qq : 32'h0;
      ADDR_GPIO2_TRI:  s_axi_rdata = C_IS_DUAL ? gpio2_tri_q : 32'h0;
      ADDR_GIER:       s_axi_rdata = C_INTERRUPT_PRESENT ? {gier_q, 31'h0} : 32'h0;
      ADDR_IP_ISR:     s_axi_rdata = C_INTERRUPT_PRESENT ? {30'h0, ip_isr_q} : 32'h0;
      ADDR_IP_IER:     s_axi_rdata = C_INTERRUPT_PRESENT ? {30'h0, ip_ier_q} : 32'h0;
      default:         s_axi_rdata = 32'h0;
    endcase
  end

  // ===========================================================================
  // AXI Response Signals
  // ===========================================================================
  assign s_axi_awready = (state_q == AXI_IDLE);
  assign s_axi_wready = (state_q == AXI_IDLE);
  assign s_axi_bvalid = (state_q == AXI_WRITE);
  assign s_axi_bresp = 2'b00;  // OKAY
  assign s_axi_arready = (state_q == AXI_IDLE);
  assign s_axi_rvalid = (state_q == AXI_READ);
  assign s_axi_rresp = 2'b00;  // OKAY

  // ===========================================================================
  // GPIO Outputs
  // ===========================================================================
  assign gpio_io_o = gpio_data_q[C_GPIO_WIDTH-1:0];
  assign gpio_io_t = gpio_tri_q[C_GPIO_WIDTH-1:0];
  assign gpio2_io_o = gpio2_data_q[C_GPIO2_WIDTH-1:0];
  assign gpio2_io_t = gpio2_tri_q[C_GPIO2_WIDTH-1:0];

endmodule
