/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

================================================================================
Watchdog Timer (WDT) Module
================================================================================
Features:
  - Configurable timeout period (up to 2^32 cycles)
  - Window mode: Must be refreshed within a time window (not too early, not too late)
  - Lock register to prevent accidental disable
  - Debug pause: Optionally pause when CPU halted
  - Reset generation with configurable pulse width
  - Early warning interrupt before reset

Register Map (32-bit, word-aligned):
  0x00: CTRL   - Control register
  0x04: LOAD   - Reload value (timeout period)
  0x08: COUNT  - Current counter value (read-only)
  0x0C: WINDOW - Window start value (for window mode)
  0x10: KEY    - Key register (unlock/refresh)
  0x14: STATUS - Status register

CTRL Register [31:0]:
  [0]     : EN       - Watchdog enable
  [1]     : RSTEN    - Reset enable (1=generate reset, 0=interrupt only)
  [2]     : WINEN    - Window mode enable
  [3]     : DBGPAUSE - Pause counter when debug halted
  [4]     : IE       - Interrupt enable (early warning)
  [7:5]   : Reserved
  [15:8]  : EWI_DIV  - Early warning divider (interrupt at COUNT < LOAD>>EWI_DIV)
  [31:16] : Reserved

STATUS Register [31:0]:
  [0]     : EWIF     - Early warning interrupt flag (W1C)
  [1]     : WDTRF    - Watchdog reset flag (set by reset, cleared by SW)
  [2]     : LOCKED   - Lock status (read-only)
  [3]     : WINVIOL  - Window violation occurred (W1C)
  [31:4]  : Reserved

KEY Register:
  Write 0x5A5A_5A5A : Refresh/kick the watchdog
  Write 0x1234_5678 : Unlock CTRL and LOAD registers
  Write 0xDEAD_BEEF : Lock CTRL and LOAD registers

================================================================================
*/

`timescale 1ns / 1ps

module watchdog
  import ceres_param::*;
#(
    parameter int RESET_PULSE_WIDTH = 16  // Reset pulse width in cycles
) (
    input  logic        clk_i,
    input  logic        rst_ni,
    // Register Interface
    input  logic        stb_i,
    input  logic [ 3:0] adr_i,        // Word address [5:2]
    input  logic [ 3:0] byte_sel_i,
    input  logic        we_i,
    input  logic [31:0] dat_i,
    output logic [31:0] dat_o,
    // Debug interface
    input  logic        dbg_halt_i,
    // Outputs
    output logic        wdt_reset_o,  // System reset output
    output logic        irq_o         // Early warning interrupt
);

  // ===========================================================================
  // Register Addresses
  // ===========================================================================
  localparam logic [3:0] REG_CTRL = 4'h0;
  localparam logic [3:0] REG_LOAD = 4'h1;
  localparam logic [3:0] REG_COUNT = 4'h2;
  localparam logic [3:0] REG_WINDOW = 4'h3;
  localparam logic [3:0] REG_KEY = 4'h4;
  localparam logic [3:0] REG_STATUS = 4'h5;

  // Key values
  localparam logic [31:0] KEY_REFRESH = 32'h5A5A_5A5A;
  localparam logic [31:0] KEY_UNLOCK = 32'h1234_5678;
  localparam logic [31:0] KEY_LOCK = 32'hDEAD_BEEF;

  // ===========================================================================
  // Registers
  // ===========================================================================
  logic [31:0] ctrl_q;
  logic [31:0] load_q;
  logic [31:0] count_q;
  logic [31:0] window_q;
  logic [31:0] status_q;
  logic        locked_q;

  // Control bits
  logic        wdt_en;
  logic        rst_en;
  logic        win_en;
  logic        dbg_pause;
  logic        int_en;
  logic [ 7:0] ewi_div;

  assign wdt_en    = ctrl_q[0];
  assign rst_en    = ctrl_q[1];
  assign win_en    = ctrl_q[2];
  assign dbg_pause = ctrl_q[3];
  assign int_en    = ctrl_q[4];
  assign ewi_div   = ctrl_q[15:8];

  // Status bits
  logic                                 ewif_q;  // Early warning interrupt flag
  logic                                 wdtrf_q;  // Watchdog reset flag
  logic                                 winviol_q;  // Window violation flag

  // Internal signals
  logic                                 count_pause;
  logic                                 refresh_req;
  logic                                 window_violation;
  logic [                         31:0] ewi_threshold;
  logic                                 ewi_triggered;

  // Reset generation
  logic [$clog2(RESET_PULSE_WIDTH)-1:0] rst_pulse_cnt;
  logic                                 rst_pulse_active;

  // ===========================================================================
  // Counter Pause Logic
  // ===========================================================================
  assign count_pause = dbg_pause & dbg_halt_i;

  // ===========================================================================
  // Early Warning Threshold
  // ===========================================================================
  assign ewi_threshold = load_q >> ewi_div;
  assign ewi_triggered = wdt_en & (count_q < ewi_threshold) & (count_q > 0);

  // ===========================================================================
  // Window Violation Detection
  // ===========================================================================
  // Violation if refresh comes before counter reaches window value
  assign window_violation = win_en & refresh_req & (count_q > window_q);

  // ===========================================================================
  // Register Write Logic
  // ===========================================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ctrl_q    <= 32'h0;
      load_q    <= 32'hFFFF_FFFF;  // Maximum timeout by default
      window_q  <= 32'h0;
      locked_q  <= 1'b0;
      ewif_q    <= 1'b0;
      wdtrf_q   <= 1'b0;
      winviol_q <= 1'b0;
    end else begin
      // Early warning flag
      if (ewi_triggered & ~ewif_q) begin
        ewif_q <= 1'b1;
      end

      // Window violation flag
      if (window_violation) begin
        winviol_q <= 1'b1;
      end

      // Register writes
      if (stb_i & we_i) begin
        case (adr_i)
          REG_CTRL: begin
            if (!locked_q) begin
              if (byte_sel_i[0]) ctrl_q[7:0] <= dat_i[7:0];
              if (byte_sel_i[1]) ctrl_q[15:8] <= dat_i[15:8];
              if (byte_sel_i[2]) ctrl_q[23:16] <= dat_i[23:16];
              if (byte_sel_i[3]) ctrl_q[31:24] <= dat_i[31:24];
            end
          end

          REG_LOAD: begin
            if (!locked_q) begin
              if (byte_sel_i[0]) load_q[7:0] <= dat_i[7:0];
              if (byte_sel_i[1]) load_q[15:8] <= dat_i[15:8];
              if (byte_sel_i[2]) load_q[23:16] <= dat_i[23:16];
              if (byte_sel_i[3]) load_q[31:24] <= dat_i[31:24];
            end
          end

          REG_WINDOW: begin
            if (!locked_q) begin
              if (byte_sel_i[0]) window_q[7:0] <= dat_i[7:0];
              if (byte_sel_i[1]) window_q[15:8] <= dat_i[15:8];
              if (byte_sel_i[2]) window_q[23:16] <= dat_i[23:16];
              if (byte_sel_i[3]) window_q[31:24] <= dat_i[31:24];
            end
          end

          REG_KEY: begin
            case (dat_i)
              KEY_UNLOCK: locked_q <= 1'b0;
              KEY_LOCK:   locked_q <= 1'b1;
              default:    ;  // KEY_REFRESH handled separately
            endcase
          end

          REG_STATUS: begin
            // W1C behavior for status flags
            if (byte_sel_i[0]) begin
              if (dat_i[0]) ewif_q <= 1'b0;
              if (dat_i[1]) wdtrf_q <= 1'b0;
              if (dat_i[3]) winviol_q <= 1'b0;
            end
          end

          default: ;
        endcase
      end

      // Set reset flag when watchdog resets (sticky until cleared)
      if (rst_pulse_active && rst_pulse_cnt == 0) begin
        wdtrf_q <= 1'b1;
      end
    end
  end

  // ===========================================================================
  // Refresh Request Detection
  // ===========================================================================
  assign refresh_req = stb_i & we_i & (adr_i == REG_KEY) & (dat_i == KEY_REFRESH);

  // ===========================================================================
  // Counter Logic
  // ===========================================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      count_q <= 32'hFFFF_FFFF;
    end else if (wdt_en) begin
      if (refresh_req & ~window_violation) begin
        // Reload counter on valid refresh
        count_q <= load_q;
      end else if (!count_pause && count_q > 0) begin
        // Decrement counter
        count_q <= count_q - 1;
      end
    end else begin
      // Watchdog disabled, keep counter at load value
      count_q <= load_q;
    end
  end

  // ===========================================================================
  // Reset Pulse Generation
  // ===========================================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rst_pulse_cnt    <= '0;
      rst_pulse_active <= 1'b0;
    end else begin
      if (wdt_en & rst_en & ((count_q == 0) | window_violation)) begin
        // Start reset pulse
        rst_pulse_active <= 1'b1;
        rst_pulse_cnt    <= RESET_PULSE_WIDTH - 1;
      end else if (rst_pulse_active) begin
        if (rst_pulse_cnt > 0) begin
          rst_pulse_cnt <= rst_pulse_cnt - 1;
        end else begin
          rst_pulse_active <= 1'b0;
        end
      end
    end
  end

  // ===========================================================================
  // Output Assignments
  // ===========================================================================
  assign wdt_reset_o = rst_pulse_active;
  assign irq_o       = int_en & ewif_q;

  // ===========================================================================
  // Read Data Mux
  // ===========================================================================
  always_comb begin
    dat_o = 32'h0;
    if (stb_i & ~we_i) begin
      case (adr_i)
        REG_CTRL:   dat_o = ctrl_q;
        REG_LOAD:   dat_o = load_q;
        REG_COUNT:  dat_o = count_q;
        REG_WINDOW: dat_o = window_q;
        REG_KEY:    dat_o = 32'h0;  // Write-only
        REG_STATUS: dat_o = {28'b0, winviol_q, locked_q, wdtrf_q, ewif_q};
        default:    dat_o = 32'h0;
      endcase
    end
  end

endmodule
