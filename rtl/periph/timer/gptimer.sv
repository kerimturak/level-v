/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  General Purpose Timer with PWM capability
  
  Features:
  - 4 independent 32-bit timers
  - 16-bit prescaler per timer
  - Up/Down counting modes
  - One-pulse mode
  - 2 Compare/Capture channels per timer
  - PWM output generation
  - Interrupt on overflow, compare match
  
  Memory Map (base 0x2000_6000, 0x40 per timer):
    Timer 0: 0x000-0x03F
    Timer 1: 0x040-0x07F
    Timer 2: 0x080-0x0BF
    Timer 3: 0x0C0-0x0FF
    
  Per-Timer Register Map (offset from timer base):
    0x00 - TIMx_CTRL   : Control register
    0x04 - TIMx_CNT    : Counter value
    0x08 - TIMx_PSC    : Prescaler (16-bit)
    0x0C - TIMx_ARR    : Auto-reload value
    0x10 - TIMx_CCR0   : Compare/Capture 0
    0x14 - TIMx_CCR1   : Compare/Capture 1
    0x18 - TIMx_SR     : Status register (W1C)
    0x1C - TIMx_IER    : Interrupt enable
    
  CTRL Register Bits:
    [0]    : EN     - Timer enable
    [1]    : DIR    - Count direction (0=up, 1=down)
    [2]    : OPM    - One-pulse mode
    [3]    : ARPE   - Auto-reload preload enable
    [5:4]  : CC0M   - Capture/Compare 0 mode (00=frozen, 01=compare, 10=PWM1, 11=PWM2)
    [7:6]  : CC1M   - Capture/Compare 1 mode
    [8]    : CC0E   - Capture/Compare 0 output enable
    [9]    : CC1E   - Capture/Compare 1 output enable
    [10]   : CC0P   - Capture/Compare 0 polarity (0=active high)
    [11]   : CC1P   - Capture/Compare 1 polarity
    
  Status Register Bits:
    [0]    : UIF    - Update interrupt flag (overflow/underflow)
    [1]    : CC0IF  - Compare/Capture 0 interrupt flag
    [2]    : CC1IF  - Compare/Capture 1 interrupt flag
*/
`timescale 1ns / 1ps

module gptimer
  import ceres_param::*;
#(
    parameter int NUM_TIMERS = 4
) (
    input logic clk_i,
    input logic rst_ni,

    // Register interface
    input  logic            stb_i,
    input  logic [     7:0] adr_i,       // 8-bit address (4 timers * 16 regs * 4 bytes)
    input  logic [     3:0] byte_sel_i,
    input  logic            we_i,
    input  logic [XLEN-1:0] dat_i,
    output logic [XLEN-1:0] dat_o,

    // PWM outputs (directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly 2 per timer)
    output logic [NUM_TIMERS*2-1:0] pwm_o,

    // Interrupt outputs (1 per timer, directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly directly OR of all timer interrupts)
    output logic [NUM_TIMERS-1:0] irq_o,
    output logic                  irq_combined_o
);

  // ============================================================================
  // Timer Register Indices
  // ============================================================================
  localparam logic [3:0] REG_CTRL = 4'h0;
  localparam logic [3:0] REG_CNT = 4'h1;
  localparam logic [3:0] REG_PSC = 4'h2;
  localparam logic [3:0] REG_ARR = 4'h3;
  localparam logic [3:0] REG_CCR0 = 4'h4;
  localparam logic [3:0] REG_CCR1 = 4'h5;
  localparam logic [3:0] REG_SR = 4'h6;
  localparam logic [3:0] REG_IER = 4'h7;

  // ============================================================================
  // Per-Timer Registers
  // ============================================================================
  logic [          31:0] ctrl_q   [NUM_TIMERS];
  logic [          31:0] cnt_q    [NUM_TIMERS];
  logic [          15:0] psc_q    [NUM_TIMERS];
  logic [          31:0] arr_q    [NUM_TIMERS];
  logic [          31:0] ccr0_q   [NUM_TIMERS];
  logic [          31:0] ccr1_q   [NUM_TIMERS];
  logic [          31:0] sr_q     [NUM_TIMERS];
  logic [          31:0] ier_q    [NUM_TIMERS];

  // Prescaler counters
  logic [          15:0] psc_cnt_q[NUM_TIMERS];

  // ============================================================================
  // Control Register Bit Extraction
  // ============================================================================
  logic [NUM_TIMERS-1:0] tim_en;
  logic [NUM_TIMERS-1:0] tim_dir;
  logic [NUM_TIMERS-1:0] tim_opm;
  logic [NUM_TIMERS-1:0] tim_arpe;
  logic [           1:0] tim_cc0m [NUM_TIMERS];
  logic [           1:0] tim_cc1m [NUM_TIMERS];
  logic [NUM_TIMERS-1:0] tim_cc0e;
  logic [NUM_TIMERS-1:0] tim_cc1e;
  logic [NUM_TIMERS-1:0] tim_cc0p;
  logic [NUM_TIMERS-1:0] tim_cc1p;

  for (genvar i = 0; i < NUM_TIMERS; i++) begin : gen_ctrl_extract
    assign tim_en[i]   = ctrl_q[i][0];
    assign tim_dir[i]  = ctrl_q[i][1];
    assign tim_opm[i]  = ctrl_q[i][2];
    assign tim_arpe[i] = ctrl_q[i][3];
    assign tim_cc0m[i] = ctrl_q[i][5:4];
    assign tim_cc1m[i] = ctrl_q[i][7:6];
    assign tim_cc0e[i] = ctrl_q[i][8];
    assign tim_cc1e[i] = ctrl_q[i][9];
    assign tim_cc0p[i] = ctrl_q[i][10];
    assign tim_cc1p[i] = ctrl_q[i][11];
  end

  // ============================================================================
  // Address Decode
  // ============================================================================
  logic [1:0] timer_sel;
  logic [3:0] reg_sel;

  assign timer_sel = adr_i[7:6];  // Which timer (0-3)
  assign reg_sel   = adr_i[5:2];  // Which register (word aligned)

  // ============================================================================
  // Timer Logic
  // ============================================================================
  logic [NUM_TIMERS-1:0] update_event;
  logic [NUM_TIMERS-1:0] cc0_match;
  logic [NUM_TIMERS-1:0] cc1_match;
  logic [NUM_TIMERS-1:0] psc_tick;

  for (genvar i = 0; i < NUM_TIMERS; i++) begin : gen_timer_logic
    // Prescaler tick
    assign psc_tick[i] = (psc_cnt_q[i] == psc_q[i]);

    // Compare match detection
    assign cc0_match[i] = (cnt_q[i] == ccr0_q[i]);
    assign cc1_match[i] = (cnt_q[i] == ccr1_q[i]);

    // Update event (overflow or underflow)
    assign update_event[i] = tim_dir[i] ? (cnt_q[i] == 0 && psc_tick[i]) : (cnt_q[i] == arr_q[i] && psc_tick[i]);
  end

  // ============================================================================
  // Counter and Status Logic
  // ============================================================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      for (int i = 0; i < NUM_TIMERS; i++) begin
        ctrl_q[i]    <= '0;
        cnt_q[i]     <= '0;
        psc_q[i]     <= '0;
        arr_q[i]     <= 32'hFFFF_FFFF;
        ccr0_q[i]    <= '0;
        ccr1_q[i]    <= '0;
        sr_q[i]      <= '0;
        ier_q[i]     <= '0;
        psc_cnt_q[i] <= '0;
      end
    end else begin
      // Timer counter logic
      for (int i = 0; i < NUM_TIMERS; i++) begin
        if (tim_en[i]) begin
          // Prescaler
          if (psc_tick[i]) begin
            psc_cnt_q[i] <= '0;

            // Counter
            if (tim_dir[i]) begin
              // Count down
              if (cnt_q[i] == 0) begin
                cnt_q[i]   <= arr_q[i];
                sr_q[i][0] <= 1'b1;  // UIF
                if (tim_opm[i]) ctrl_q[i][0] <= 1'b0;  // Disable in OPM
              end else begin
                cnt_q[i] <= cnt_q[i] - 1;
              end
            end else begin
              // Count up
              if (cnt_q[i] == arr_q[i]) begin
                cnt_q[i]   <= '0;
                sr_q[i][0] <= 1'b1;  // UIF
                if (tim_opm[i]) ctrl_q[i][0] <= 1'b0;  // Disable in OPM
              end else begin
                cnt_q[i] <= cnt_q[i] + 1;
              end
            end
          end else begin
            psc_cnt_q[i] <= psc_cnt_q[i] + 1;
          end

          // Compare match flags
          if (cc0_match[i]) sr_q[i][1] <= 1'b1;
          if (cc1_match[i]) sr_q[i][2] <= 1'b1;
        end
      end

      // Register writes
      if (stb_i && we_i) begin
        case (reg_sel)
          REG_CTRL: begin
            if (byte_sel_i[0]) ctrl_q[timer_sel][7:0] <= dat_i[7:0];
            if (byte_sel_i[1]) ctrl_q[timer_sel][15:8] <= dat_i[15:8];
            if (byte_sel_i[2]) ctrl_q[timer_sel][23:16] <= dat_i[23:16];
            if (byte_sel_i[3]) ctrl_q[timer_sel][31:24] <= dat_i[31:24];
          end

          REG_CNT: begin
            if (byte_sel_i[0]) cnt_q[timer_sel][7:0] <= dat_i[7:0];
            if (byte_sel_i[1]) cnt_q[timer_sel][15:8] <= dat_i[15:8];
            if (byte_sel_i[2]) cnt_q[timer_sel][23:16] <= dat_i[23:16];
            if (byte_sel_i[3]) cnt_q[timer_sel][31:24] <= dat_i[31:24];
          end

          REG_PSC: begin
            if (byte_sel_i[0]) psc_q[timer_sel][7:0] <= dat_i[7:0];
            if (byte_sel_i[1]) psc_q[timer_sel][15:8] <= dat_i[15:8];
          end

          REG_ARR: begin
            if (byte_sel_i[0]) arr_q[timer_sel][7:0] <= dat_i[7:0];
            if (byte_sel_i[1]) arr_q[timer_sel][15:8] <= dat_i[15:8];
            if (byte_sel_i[2]) arr_q[timer_sel][23:16] <= dat_i[23:16];
            if (byte_sel_i[3]) arr_q[timer_sel][31:24] <= dat_i[31:24];
          end

          REG_CCR0: begin
            if (byte_sel_i[0]) ccr0_q[timer_sel][7:0] <= dat_i[7:0];
            if (byte_sel_i[1]) ccr0_q[timer_sel][15:8] <= dat_i[15:8];
            if (byte_sel_i[2]) ccr0_q[timer_sel][23:16] <= dat_i[23:16];
            if (byte_sel_i[3]) ccr0_q[timer_sel][31:24] <= dat_i[31:24];
          end

          REG_CCR1: begin
            if (byte_sel_i[0]) ccr1_q[timer_sel][7:0] <= dat_i[7:0];
            if (byte_sel_i[1]) ccr1_q[timer_sel][15:8] <= dat_i[15:8];
            if (byte_sel_i[2]) ccr1_q[timer_sel][23:16] <= dat_i[23:16];
            if (byte_sel_i[3]) ccr1_q[timer_sel][31:24] <= dat_i[31:24];
          end

          REG_SR: begin
            // Write-1-to-clear
            if (byte_sel_i[0]) sr_q[timer_sel][7:0] <= sr_q[timer_sel][7:0] & ~dat_i[7:0];
            if (byte_sel_i[1]) sr_q[timer_sel][15:8] <= sr_q[timer_sel][15:8] & ~dat_i[15:8];
            if (byte_sel_i[2]) sr_q[timer_sel][23:16] <= sr_q[timer_sel][23:16] & ~dat_i[23:16];
            if (byte_sel_i[3]) sr_q[timer_sel][31:24] <= sr_q[timer_sel][31:24] & ~dat_i[31:24];
          end

          REG_IER: begin
            if (byte_sel_i[0]) ier_q[timer_sel][7:0] <= dat_i[7:0];
            if (byte_sel_i[1]) ier_q[timer_sel][15:8] <= dat_i[15:8];
            if (byte_sel_i[2]) ier_q[timer_sel][23:16] <= dat_i[23:16];
            if (byte_sel_i[3]) ier_q[timer_sel][31:24] <= dat_i[31:24];
          end

          default: ;
        endcase
      end
    end
  end

  // ============================================================================
  // Register Read
  // ============================================================================
  always_comb begin
    dat_o = '0;
    case (reg_sel)
      REG_CTRL: dat_o = ctrl_q[timer_sel];
      REG_CNT:  dat_o = cnt_q[timer_sel];
      REG_PSC:  dat_o = {16'b0, psc_q[timer_sel]};
      REG_ARR:  dat_o = arr_q[timer_sel];
      REG_CCR0: dat_o = ccr0_q[timer_sel];
      REG_CCR1: dat_o = ccr1_q[timer_sel];
      REG_SR:   dat_o = sr_q[timer_sel];
      REG_IER:  dat_o = ier_q[timer_sel];
      default:  dat_o = '0;
    endcase
  end

  // ============================================================================
  // PWM Output Generation
  // ============================================================================
  for (genvar i = 0; i < NUM_TIMERS; i++) begin : gen_pwm
    logic pwm0_raw, pwm1_raw;

    // CC0 PWM
    always_comb begin
      case (tim_cc0m[i])
        2'b00: pwm0_raw = 1'b0;  // Frozen
        2'b01: pwm0_raw = cc0_match[i];  // Toggle on match (simple compare)
        2'b10: pwm0_raw = (cnt_q[i] < ccr0_q[i]);  // PWM mode 1
        2'b11: pwm0_raw = (cnt_q[i] >= ccr0_q[i]);  // PWM mode 2
      endcase
    end

    // CC1 PWM
    always_comb begin
      case (tim_cc1m[i])
        2'b00: pwm1_raw = 1'b0;
        2'b01: pwm1_raw = cc1_match[i];
        2'b10: pwm1_raw = (cnt_q[i] < ccr1_q[i]);
        2'b11: pwm1_raw = (cnt_q[i] >= ccr1_q[i]);
      endcase
    end

    // Apply polarity and output enable
    assign pwm_o[i*2]   = tim_cc0e[i] ? (pwm0_raw ^ tim_cc0p[i]) : 1'b0;
    assign pwm_o[i*2+1] = tim_cc1e[i] ? (pwm1_raw ^ tim_cc1p[i]) : 1'b0;
  end

  // ============================================================================
  // Interrupt Generation
  // ============================================================================
  for (genvar i = 0; i < NUM_TIMERS; i++) begin : gen_irq
    assign irq_o[i] = |(sr_q[i] & ier_q[i]);
  end

  assign irq_combined_o = |irq_o;

endmodule
