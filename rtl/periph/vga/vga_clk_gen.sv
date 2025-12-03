/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

================================================================================
VGA Pixel Clock Generator
================================================================================
Description:
  Generates 25.175 MHz pixel clock from system clock for VGA 640x480@60Hz.
  
  Options:
    1. For FPGA: Use PLL/MMCM (Xilinx) or PLL (Intel/Altera)
    2. For simulation: Simple clock divider (approximate)
  
  From common system clocks:
    - 100 MHz / 4 = 25 MHz (close enough for most monitors)
    - 50 MHz / 2 = 25 MHz
    - 25 MHz = direct use

  For precise 25.175 MHz, use FPGA PLL with:
    - Xilinx: MMCM/PLL with exact fractional division
    - Actual frequency tolerance is ±0.5% for VGA
================================================================================
*/

`timescale 1ns / 1ps

module vga_clk_gen #(
    parameter int SYS_CLK_FREQ   = 100_000_000,  // System clock frequency
    parameter int PIXEL_CLK_FREQ = 25_175_000    // Target pixel clock
) (
    input  logic clk_i,
    input  logic rst_ni,
    output logic pixel_clk_o,
    output logic locked_o
);

  // Calculate divider (integer approximation)
  localparam int DIVIDER = SYS_CLK_FREQ / PIXEL_CLK_FREQ;
  localparam int DIV_BITS = $clog2(DIVIDER);

  // For simulation/simple implementation
  logic [DIV_BITS-1:0] div_cnt;
  logic                pixel_clk_reg;

  generate
    if (DIVIDER <= 1) begin : gen_direct
      // Direct connection if frequencies match
      assign pixel_clk_o = clk_i;
      assign locked_o    = 1'b1;

    end else if (DIVIDER == 2) begin : gen_div2
      // Simple divide by 2
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          pixel_clk_reg <= 1'b0;
        end else begin
          pixel_clk_reg <= ~pixel_clk_reg;
        end
      end
      assign pixel_clk_o = pixel_clk_reg;
      assign locked_o    = 1'b1;

    end else begin : gen_divN
      // Divide by N (generates 50% duty cycle at half the target frequency)
      // For proper 50% duty cycle, toggle at DIVIDER/2
      localparam int HALF_DIV = DIVIDER / 2;

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          div_cnt       <= '0;
          pixel_clk_reg <= 1'b0;
        end else begin
          if (div_cnt >= DIV_BITS'(HALF_DIV - 1)) begin
            div_cnt       <= '0;
            pixel_clk_reg <= ~pixel_clk_reg;
          end else begin
            div_cnt <= div_cnt + 1;
          end
        end
      end
      assign pixel_clk_o = pixel_clk_reg;
      assign locked_o    = 1'b1;
    end
  endgenerate

endmodule


// =============================================================================
// Xilinx MMCM Wrapper for Precise Pixel Clock
// =============================================================================
// Use this for production FPGA designs that need exact 25.175 MHz

/* verilator lint_off DECLFILENAME */
module vga_clk_mmcm (
    input  logic clk_i,        // 100 MHz input
    input  logic rst_ni,
    output logic pixel_clk_o,  // 25.175 MHz output
    output logic locked_o
);

`ifdef XILINX_FPGA
  // Xilinx MMCM instantiation
  // Parameters calculated for 100 MHz -> 25.175 MHz
  // FVCO = 100 * 10.07 / 1 = 1007 MHz
  // FOUT = 1007 / 40 = 25.175 MHz

  wire clk_fb;
  wire pixel_clk_unbuf;

  MMCME2_BASE #(
      .BANDWIDTH         ("OPTIMIZED"),
      .CLKOUT0_DIVIDE_F  (40.0),         // 25.175 MHz
      .CLKOUT0_DUTY_CYCLE(0.5),
      .CLKOUT0_PHASE     (0.0),
      .CLKIN1_PERIOD     (10.0),         // 100 MHz = 10ns period
      .CLKFBOUT_MULT_F   (10.07),        // VCO = 1007 MHz
      .CLKFBOUT_PHASE    (0.0),
      .DIVCLK_DIVIDE     (1),
      .REF_JITTER1       (0.0),
      .STARTUP_WAIT      ("FALSE")
  ) mmcm_inst (
      .CLKOUT0  (pixel_clk_unbuf),
      .CLKOUT0B (),
      .CLKOUT1  (),
      .CLKOUT1B (),
      .CLKOUT2  (),
      .CLKOUT2B (),
      .CLKOUT3  (),
      .CLKOUT3B (),
      .CLKOUT4  (),
      .CLKOUT5  (),
      .CLKOUT6  (),
      .CLKFBOUT (clk_fb),
      .CLKFBOUTB(),
      .LOCKED   (locked_o),
      .CLKIN1   (clk_i),
      .PWRDWN   (1'b0),
      .RST      (~rst_ni),
      .CLKFBIN  (clk_fb)
  );

  BUFG bufg_inst (
      .I(pixel_clk_unbuf),
      .O(pixel_clk_o)
  );

`else
  // Fallback for simulation
  vga_clk_gen #(
      .SYS_CLK_FREQ  (100_000_000),
      .PIXEL_CLK_FREQ(25_000_000)
  ) clk_gen (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .pixel_clk_o(pixel_clk_o),
      .locked_o   (locked_o)
  );
`endif

endmodule
/* verilator lint_on DECLFILENAME */
