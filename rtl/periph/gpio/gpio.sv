/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  GPIO (General Purpose Input/Output) Controller
  
  Features:
  - 32-bit bidirectional GPIO
  - Per-pin direction control
  - Atomic set/clear/toggle operations
  - Pull-up/pull-down configuration
  - Interrupt on change (rising/falling/both edges)
  - Edge detection for interrupts
  
  Register Map (offset from base 0x2000_4000):
    0x00 - GPIO_DIR    : Direction (0=input, 1=output)
    0x04 - GPIO_OUT    : Output data register
    0x08 - GPIO_IN     : Input data register (read-only)
    0x0C - GPIO_SET    : Atomic bit set (write-only)
    0x10 - GPIO_CLR    : Atomic bit clear (write-only)
    0x14 - GPIO_TGL    : Atomic bit toggle (write-only)
    0x18 - GPIO_PUE    : Pull-up enable
    0x1C - GPIO_PDE    : Pull-down enable
    0x20 - GPIO_IE     : Interrupt enable
    0x24 - GPIO_IS     : Interrupt status (write-1-to-clear)
    0x28 - GPIO_IBE    : Interrupt both edges
    0x2C - GPIO_IEV    : Interrupt event (0=falling, 1=rising, when IBE=0)
*/
`timescale 1ns / 1ps

module gpio
  import ceres_param::*;
#(
    parameter int GPIO_WIDTH = 32
) (
    input logic clk_i,
    input logic rst_ni,

    // Register interface (PBUS style)
    input  logic            stb_i,
    input  logic [     3:0] adr_i,       // 4-bit address for 12 registers
    input  logic [     3:0] byte_sel_i,
    input  logic            we_i,
    input  logic [XLEN-1:0] dat_i,
    output logic [XLEN-1:0] dat_o,

    // GPIO pins
    input  logic [GPIO_WIDTH-1:0] gpio_i,      // Input from pads
    output logic [GPIO_WIDTH-1:0] gpio_o,      // Output to pads
    output logic [GPIO_WIDTH-1:0] gpio_oe_o,   // Output enable (active high)
    output logic [GPIO_WIDTH-1:0] gpio_pue_o,  // Pull-up enable
    output logic [GPIO_WIDTH-1:0] gpio_pde_o,  // Pull-down enable

    // Interrupt output
    output logic irq_o
);

  // ============================================================================
  // Register Addresses
  // ============================================================================
  localparam logic [3:0] ADDR_DIR = 4'h0;
  localparam logic [3:0] ADDR_OUT = 4'h1;
  localparam logic [3:0] ADDR_IN = 4'h2;
  localparam logic [3:0] ADDR_SET = 4'h3;
  localparam logic [3:0] ADDR_CLR = 4'h4;
  localparam logic [3:0] ADDR_TGL = 4'h5;
  localparam logic [3:0] ADDR_PUE = 4'h6;
  localparam logic [3:0] ADDR_PDE = 4'h7;
  localparam logic [3:0] ADDR_IE = 4'h8;
  localparam logic [3:0] ADDR_IS = 4'h9;
  localparam logic [3:0] ADDR_IBE = 4'hA;
  localparam logic [3:0] ADDR_IEV = 4'hB;

  // ============================================================================
  // Registers
  // ============================================================================
  logic [GPIO_WIDTH-1:0] dir_q;  // Direction: 0=input, 1=output
  logic [GPIO_WIDTH-1:0] out_q;  // Output data
  logic [GPIO_WIDTH-1:0] pue_q;  // Pull-up enable
  logic [GPIO_WIDTH-1:0] pde_q;  // Pull-down enable
  logic [GPIO_WIDTH-1:0] ie_q;  // Interrupt enable
  logic [GPIO_WIDTH-1:0] is_q;  // Interrupt status
  logic [GPIO_WIDTH-1:0] ibe_q;  // Interrupt both edges
  logic [GPIO_WIDTH-1:0] iev_q;  // Interrupt event (edge select)

  // ============================================================================
  // Input Synchronization (2-stage synchronizer for metastability)
  // ============================================================================
  logic [GPIO_WIDTH-1:0] gpio_sync1_q;
  logic [GPIO_WIDTH-1:0] gpio_sync2_q;
  logic [GPIO_WIDTH-1:0] gpio_prev_q;  // Previous value for edge detection

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      gpio_sync1_q <= '0;
      gpio_sync2_q <= '0;
      gpio_prev_q  <= '0;
    end else begin
      gpio_sync1_q <= gpio_i;
      gpio_sync2_q <= gpio_sync1_q;
      gpio_prev_q  <= gpio_sync2_q;
    end
  end

  // Synchronized input value
  wire  [GPIO_WIDTH-1:0] gpio_in = gpio_sync2_q;

  // ============================================================================
  // Edge Detection
  // ============================================================================
  logic [GPIO_WIDTH-1:0] rising_edge;
  logic [GPIO_WIDTH-1:0] falling_edge;
  logic [GPIO_WIDTH-1:0] any_edge;

  assign rising_edge  = gpio_in & ~gpio_prev_q;  // 0->1 transition
  assign falling_edge = ~gpio_in & gpio_prev_q;  // 1->0 transition
  assign any_edge     = rising_edge | falling_edge;

  // ============================================================================
  // Interrupt Logic
  // ============================================================================
  logic [GPIO_WIDTH-1:0] irq_trigger;

  // Determine which edges trigger interrupts
  always_comb begin
    for (int i = 0; i < GPIO_WIDTH; i++) begin
      if (ibe_q[i]) begin
        // Both edges
        irq_trigger[i] = any_edge[i];
      end else if (iev_q[i]) begin
        // Rising edge only
        irq_trigger[i] = rising_edge[i];
      end else begin
        // Falling edge only
        irq_trigger[i] = falling_edge[i];
      end
    end
  end

  // Combined interrupt output
  assign irq_o = |(is_q & ie_q);

  // ============================================================================
  // Register Write Logic
  // ============================================================================
  logic reg_write;
  assign reg_write = stb_i && we_i;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      dir_q <= '0;  // All inputs by default
      out_q <= '0;
      pue_q <= '0;
      pde_q <= '0;
      ie_q  <= '0;
      is_q  <= '0;
      ibe_q <= '0;
      iev_q <= '0;
    end else begin
      // Set interrupt status on edge detection (regardless of ie_q)
      is_q <= is_q | irq_trigger;

      // Register writes
      if (reg_write) begin
        case (adr_i)
          ADDR_DIR: begin
            if (byte_sel_i[0]) dir_q[7:0] <= dat_i[7:0];
            if (byte_sel_i[1]) dir_q[15:8] <= dat_i[15:8];
            if (byte_sel_i[2]) dir_q[23:16] <= dat_i[23:16];
            if (byte_sel_i[3]) dir_q[31:24] <= dat_i[31:24];
          end

          ADDR_OUT: begin
            if (byte_sel_i[0]) out_q[7:0] <= dat_i[7:0];
            if (byte_sel_i[1]) out_q[15:8] <= dat_i[15:8];
            if (byte_sel_i[2]) out_q[23:16] <= dat_i[23:16];
            if (byte_sel_i[3]) out_q[31:24] <= dat_i[31:24];
          end

          ADDR_SET: begin
            // Atomic set: write 1 to set bits
            if (byte_sel_i[0]) out_q[7:0] <= out_q[7:0] | dat_i[7:0];
            if (byte_sel_i[1]) out_q[15:8] <= out_q[15:8] | dat_i[15:8];
            if (byte_sel_i[2]) out_q[23:16] <= out_q[23:16] | dat_i[23:16];
            if (byte_sel_i[3]) out_q[31:24] <= out_q[31:24] | dat_i[31:24];
          end

          ADDR_CLR: begin
            // Atomic clear: write 1 to clear bits
            if (byte_sel_i[0]) out_q[7:0] <= out_q[7:0] & ~dat_i[7:0];
            if (byte_sel_i[1]) out_q[15:8] <= out_q[15:8] & ~dat_i[15:8];
            if (byte_sel_i[2]) out_q[23:16] <= out_q[23:16] & ~dat_i[23:16];
            if (byte_sel_i[3]) out_q[31:24] <= out_q[31:24] & ~dat_i[31:24];
          end

          ADDR_TGL: begin
            // Atomic toggle: write 1 to toggle bits
            if (byte_sel_i[0]) out_q[7:0] <= out_q[7:0] ^ dat_i[7:0];
            if (byte_sel_i[1]) out_q[15:8] <= out_q[15:8] ^ dat_i[15:8];
            if (byte_sel_i[2]) out_q[23:16] <= out_q[23:16] ^ dat_i[23:16];
            if (byte_sel_i[3]) out_q[31:24] <= out_q[31:24] ^ dat_i[31:24];
          end

          ADDR_PUE: begin
            if (byte_sel_i[0]) pue_q[7:0] <= dat_i[7:0];
            if (byte_sel_i[1]) pue_q[15:8] <= dat_i[15:8];
            if (byte_sel_i[2]) pue_q[23:16] <= dat_i[23:16];
            if (byte_sel_i[3]) pue_q[31:24] <= dat_i[31:24];
          end

          ADDR_PDE: begin
            if (byte_sel_i[0]) pde_q[7:0] <= dat_i[7:0];
            if (byte_sel_i[1]) pde_q[15:8] <= dat_i[15:8];
            if (byte_sel_i[2]) pde_q[23:16] <= dat_i[23:16];
            if (byte_sel_i[3]) pde_q[31:24] <= dat_i[31:24];
          end

          ADDR_IE: begin
            if (byte_sel_i[0]) ie_q[7:0] <= dat_i[7:0];
            if (byte_sel_i[1]) ie_q[15:8] <= dat_i[15:8];
            if (byte_sel_i[2]) ie_q[23:16] <= dat_i[23:16];
            if (byte_sel_i[3]) ie_q[31:24] <= dat_i[31:24];
          end

          ADDR_IS: begin
            // Write-1-to-clear: writing 1 clears the bit
            if (byte_sel_i[0]) is_q[7:0] <= is_q[7:0] & ~dat_i[7:0];
            if (byte_sel_i[1]) is_q[15:8] <= is_q[15:8] & ~dat_i[15:8];
            if (byte_sel_i[2]) is_q[23:16] <= is_q[23:16] & ~dat_i[23:16];
            if (byte_sel_i[3]) is_q[31:24] <= is_q[31:24] & ~dat_i[31:24];
          end

          ADDR_IBE: begin
            if (byte_sel_i[0]) ibe_q[7:0] <= dat_i[7:0];
            if (byte_sel_i[1]) ibe_q[15:8] <= dat_i[15:8];
            if (byte_sel_i[2]) ibe_q[23:16] <= dat_i[23:16];
            if (byte_sel_i[3]) ibe_q[31:24] <= dat_i[31:24];
          end

          ADDR_IEV: begin
            if (byte_sel_i[0]) iev_q[7:0] <= dat_i[7:0];
            if (byte_sel_i[1]) iev_q[15:8] <= dat_i[15:8];
            if (byte_sel_i[2]) iev_q[23:16] <= dat_i[23:16];
            if (byte_sel_i[3]) iev_q[31:24] <= dat_i[31:24];
          end

          default: ;  // No operation for undefined addresses
        endcase
      end
    end
  end

  // ============================================================================
  // Register Read Logic
  // ============================================================================
  always_comb begin
    dat_o = '0;
    case (adr_i)
      ADDR_DIR: dat_o = dir_q;
      ADDR_OUT: dat_o = out_q;
      ADDR_IN:  dat_o = gpio_in;
      ADDR_SET: dat_o = out_q;  // Reading SET returns current OUT value
      ADDR_CLR: dat_o = out_q;  // Reading CLR returns current OUT value
      ADDR_TGL: dat_o = out_q;  // Reading TGL returns current OUT value
      ADDR_PUE: dat_o = pue_q;
      ADDR_PDE: dat_o = pde_q;
      ADDR_IE:  dat_o = ie_q;
      ADDR_IS:  dat_o = is_q;
      ADDR_IBE: dat_o = ibe_q;
      ADDR_IEV: dat_o = iev_q;
      default:  dat_o = '0;
    endcase
  end

  // ============================================================================
  // Output Assignments
  // ============================================================================
  assign gpio_o    = out_q;
  assign gpio_oe_o = dir_q;   // OE matches direction (1=output)
  assign gpio_pue_o = pue_q;
  assign gpio_pde_o = pde_q;

endmodule
