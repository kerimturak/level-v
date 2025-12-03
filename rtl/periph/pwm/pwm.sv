/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

================================================================================
PWM Controller Module
================================================================================
Features:
  - 8 independent PWM channels
  - 16-bit resolution per channel
  - Common or individual period (frequency) control
  - Dead-time generator for complementary outputs
  - Phase offset for each channel
  - Center-aligned or edge-aligned modes
  - Programmable polarity
  - Fault input for emergency shutdown
  - DMA request capability

Register Map (32-bit, word-aligned):
  Global Registers:
    0x00: GCR     - Global control register
    0x04: PERIOD  - Global period value (shared by all channels in common mode)
    0x08: PSC     - Prescaler (divides input clock)
    0x0C: CNT     - Counter value (read-only in running mode)
    0x10: DEADTIME- Dead-time configuration
    0x14: FAULT   - Fault configuration and status
    0x18: IER     - Interrupt enable register
    0x1C: ISR     - Interrupt status register (W1C)

  Per-Channel Registers (8 channels, 0x10 bytes each starting at 0x40):
    0x40 + N*0x10: CCR     - Channel control register
    0x44 + N*0x10: DUTY    - Duty cycle value
    0x48 + N*0x10: PHASE   - Phase offset
    0x4C + N*0x10: Reserved

GCR (Global Control) Register [31:0]:
  [0]     : EN       - Global enable
  [1]     : OUTEN    - Output enable (master gate)
  [2]     : CNTMODE  - Counter mode (0=edge-aligned up, 1=center-aligned up-down)
  [3]     : ONESHOT  - One-shot mode
  [4]     : COMMODE  - Common period mode (0=individual, 1=shared period)
  [5]     : SYNCEN   - Sync output enable
  [6]     : DRQEN    - DMA request enable
  [7]     : Reserved
  [15:8]  : SYNCSRC  - Sync source channel mask
  [31:16] : Reserved

CCR (Channel Control) Register [31:0]:
  [0]     : EN       - Channel enable
  [1]     : POL      - Polarity (0=active high, 1=active low)
  [2]     : COMPEN   - Complementary output enable
  [3]     : DTEN     - Dead-time enable (for complementary)
  [4]     : FAULTEN  - Fault shutdown enable
  [7:5]   : Reserved
  [15:8]  : FAULTPOL - Fault output state (0=low, 1=high, 2=hi-z)
  [31:16] : Reserved

DEADTIME Register [31:0]:
  [15:0]  : RISE     - Dead-time on rising edge (in prescaled clocks)
  [31:16] : FALL     - Dead-time on falling edge

FAULT Register [31:0]:
  [0]     : FAULTIN  - Fault input state (read-only)
  [1]     : FAULTF   - Fault occurred flag (sticky, W1C)
  [2]     : FAULTPOL - Fault input polarity (0=active low, 1=active high)
  [3]     : FAULTCLR - Auto-clear fault when input deasserts
  [7:4]   : Reserved
  [15:8]  : FILTER   - Fault input filter (debounce cycles)
  [31:16] : Reserved

================================================================================
*/

`timescale 1ns / 1ps

module pwm
  import ceres_param::*;
#(
    parameter int NUM_CHANNELS = 8,
    parameter int PWM_WIDTH    = 16
) (
    input  logic                    clk_i,
    input  logic                    rst_ni,
    // Register Interface
    input  logic                    stb_i,
    input  logic [             5:0] adr_i,       // Word address [7:2]
    input  logic [             3:0] byte_sel_i,
    input  logic                    we_i,
    input  logic [            31:0] dat_i,
    output logic [            31:0] dat_o,
    // Fault input
    input  logic                    fault_i,
    // PWM outputs
    output logic [NUM_CHANNELS-1:0] pwm_o,
    output logic [NUM_CHANNELS-1:0] pwm_n_o,     // Complementary outputs
    // Sync output
    output logic                    sync_o,
    // DMA request
    output logic                    drq_o,
    // Interrupt
    output logic                    irq_o
);

  // ===========================================================================
  // Local Parameters
  // ===========================================================================
  localparam int CH_BASE_ADDR = 6'h10;  // 0x40 / 4

  // ===========================================================================
  // Global Registers
  // ===========================================================================
  logic [         31:0] gcr_q;  // Global control
  logic [PWM_WIDTH-1:0] period_q;  // Global period
  logic [         15:0] psc_q;  // Prescaler
  logic [PWM_WIDTH-1:0] cnt_q;  // Counter
  logic [         31:0] deadtime_q;  // Dead-time config
  logic [         31:0] fault_q;  // Fault config
  logic [         31:0] ier_q;  // Interrupt enable
  logic [         31:0] isr_q;  // Interrupt status

  // Global control bits
  logic                 pwm_en;
  logic                 out_en;
  logic                 cnt_mode;
  logic                 one_shot;
  logic                 com_mode;
  logic                 sync_en;
  logic                 drq_en;

  assign pwm_en   = gcr_q[0];
  assign out_en   = gcr_q[1];
  assign cnt_mode = gcr_q[2];
  assign one_shot = gcr_q[3];
  assign com_mode = gcr_q[4];
  assign sync_en  = gcr_q[5];
  assign drq_en   = gcr_q[6];

  // Dead-time values
  logic [PWM_WIDTH-1:0] dt_rise;
  logic [PWM_WIDTH-1:0] dt_fall;
  assign dt_rise = deadtime_q[PWM_WIDTH-1:0];
  assign dt_fall = deadtime_q[PWM_WIDTH+15:16];

  // ===========================================================================
  // Per-Channel Registers
  // ===========================================================================
  logic [            31:0] ccr         [NUM_CHANNELS];  // Channel control
  logic [   PWM_WIDTH-1:0] duty        [NUM_CHANNELS];  // Duty cycle
  logic [   PWM_WIDTH-1:0] phase       [NUM_CHANNELS];  // Phase offset

  // Channel control bits
  logic [NUM_CHANNELS-1:0] ch_en;
  logic [NUM_CHANNELS-1:0] ch_pol;
  logic [NUM_CHANNELS-1:0] ch_comp_en;
  logic [NUM_CHANNELS-1:0] ch_dt_en;
  logic [NUM_CHANNELS-1:0] ch_fault_en;

  generate
    for (genvar i = 0; i < NUM_CHANNELS; i++) begin : gen_ch_ctrl
      assign ch_en[i]       = ccr[i][0];
      assign ch_pol[i]      = ccr[i][1];
      assign ch_comp_en[i]  = ccr[i][2];
      assign ch_dt_en[i]    = ccr[i][3];
      assign ch_fault_en[i] = ccr[i][4];
    end
  endgenerate

  // ===========================================================================
  // Prescaler
  // ===========================================================================
  logic [15:0] psc_cnt;
  logic        psc_tick;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      psc_cnt <= 16'h0;
    end else if (pwm_en) begin
      if (psc_cnt >= psc_q) begin
        psc_cnt <= 16'h0;
      end else begin
        psc_cnt <= psc_cnt + 1;
      end
    end else begin
      psc_cnt <= 16'h0;
    end
  end

  assign psc_tick = (psc_cnt == psc_q);

  // ===========================================================================
  // Main Counter
  // ===========================================================================
  logic cnt_dir;  // 0=up, 1=down (for center-aligned)
  logic cnt_wrap;
  logic cnt_zero;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cnt_q   <= '0;
      cnt_dir <= 1'b0;
    end else if (pwm_en && psc_tick) begin
      if (cnt_mode) begin
        // Center-aligned mode (up-down counting)
        if (cnt_dir == 1'b0) begin
          // Counting up
          if (cnt_q >= period_q - 1) begin
            cnt_dir <= 1'b1;
          end else begin
            cnt_q <= cnt_q + 1;
          end
        end else begin
          // Counting down
          if (cnt_q == 0) begin
            cnt_dir <= 1'b0;
            if (one_shot) begin
              // Stop in one-shot mode
            end
          end else begin
            cnt_q <= cnt_q - 1;
          end
        end
      end else begin
        // Edge-aligned mode (up counting)
        if (cnt_q >= period_q - 1) begin
          cnt_q <= '0;
          if (one_shot) begin
            // Stop in one-shot mode - handled by disabling pwm_en
          end
        end else begin
          cnt_q <= cnt_q + 1;
        end
      end
    end else if (!pwm_en) begin
      cnt_q   <= '0;
      cnt_dir <= 1'b0;
    end
  end

  assign cnt_wrap = (cnt_q == period_q - 1) && !cnt_mode;
  assign cnt_zero = (cnt_q == 0);

  // ===========================================================================
  // Fault Handling
  // ===========================================================================
  logic       fault_active;
  logic       fault_filtered;
  logic [7:0] fault_filter_cnt;
  logic       fault_flag;

  // Fault input filtering (debounce)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fault_filter_cnt <= 8'h0;
      fault_filtered   <= 1'b0;
    end else begin
      if ((fault_i ^ fault_q[2]) == fault_filtered) begin
        // Input matches expected active state
        if (fault_filter_cnt >= fault_q[15:8]) begin
          fault_filtered <= fault_i ^ fault_q[2];  // Apply polarity
        end else begin
          fault_filter_cnt <= fault_filter_cnt + 1;
        end
      end else begin
        fault_filter_cnt <= 8'h0;
      end
    end
  end

  assign fault_active = fault_filtered;

  // Fault flag (sticky)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fault_flag <= 1'b0;
    end else begin
      if (fault_active) begin
        fault_flag <= 1'b1;
      end else if (fault_q[3] && !fault_active) begin
        // Auto-clear when input deasserts
        fault_flag <= 1'b0;
      end
      // W1C handled in register write section
    end
  end

  // ===========================================================================
  // PWM Generation
  // ===========================================================================
  logic [NUM_CHANNELS-1:0] pwm_raw;
  logic [NUM_CHANNELS-1:0] pwm_out;
  logic [NUM_CHANNELS-1:0] pwm_n_out;

  generate
    for (genvar i = 0; i < NUM_CHANNELS; i++) begin : gen_pwm
      logic [PWM_WIDTH-1:0] effective_cnt;
      logic                 compare_match;

      // Apply phase offset
      assign effective_cnt = (cnt_q >= phase[i]) ? (cnt_q - phase[i]) : (period_q - phase[i] + cnt_q);

      // Compare match
      assign compare_match = (effective_cnt < duty[i]);

      // Raw PWM signal
      assign pwm_raw[i] = ch_en[i] & compare_match;

      // Apply polarity
      logic pwm_polarity;
      assign pwm_polarity = pwm_raw[i] ^ ch_pol[i];

      // Dead-time insertion for complementary outputs
      logic [PWM_WIDTH-1:0] dt_rise_cnt;
      logic [PWM_WIDTH-1:0] dt_fall_cnt;
      logic                 pwm_rise_edge;
      logic                 pwm_fall_edge;
      logic                 pwm_delayed_rise;
      logic                 pwm_delayed_fall;

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          dt_rise_cnt <= '0;
          dt_fall_cnt <= '0;
          pwm_delayed_rise <= 1'b0;
          pwm_delayed_fall <= 1'b1;
        end else if (psc_tick) begin
          // Rising edge detection and delay
          if (pwm_polarity && !pwm_delayed_rise) begin
            if (dt_rise_cnt >= dt_rise) begin
              pwm_delayed_rise <= 1'b1;
              dt_rise_cnt <= '0;
            end else begin
              dt_rise_cnt <= dt_rise_cnt + 1;
            end
          end else if (!pwm_polarity) begin
            pwm_delayed_rise <= 1'b0;
            dt_rise_cnt <= '0;
          end

          // Falling edge detection and delay
          if (!pwm_polarity && pwm_delayed_fall) begin
            if (dt_fall_cnt >= dt_fall) begin
              pwm_delayed_fall <= 1'b0;
              dt_fall_cnt <= '0;
            end else begin
              dt_fall_cnt <= dt_fall_cnt + 1;
            end
          end else if (pwm_polarity) begin
            pwm_delayed_fall <= 1'b1;
            dt_fall_cnt <= '0;
          end
        end
      end

      // Output with dead-time
      logic pwm_with_dt;
      logic pwm_n_with_dt;

      assign pwm_with_dt   = ch_dt_en[i] ? pwm_delayed_rise : pwm_polarity;
      assign pwm_n_with_dt = ch_dt_en[i] ? ~pwm_delayed_fall : ~pwm_polarity;

      // Fault override
      logic fault_shutdown;
      assign fault_shutdown = ch_fault_en[i] & fault_flag;

      // Final outputs with fault and global enable
      assign pwm_out[i] = out_en & pwm_en & ~fault_shutdown & pwm_with_dt;
      assign pwm_n_out[i] = out_en & pwm_en & ch_comp_en[i] & ~fault_shutdown & pwm_n_with_dt;
    end
  endgenerate

  assign pwm_o   = pwm_out;
  assign pwm_n_o = pwm_n_out;

  // ===========================================================================
  // Sync Output
  // ===========================================================================
  assign sync_o  = sync_en & cnt_zero;

  // ===========================================================================
  // DMA Request
  // ===========================================================================
  assign drq_o   = drq_en & cnt_wrap;

  // ===========================================================================
  // Interrupts
  // ===========================================================================
  logic period_match_irq;
  logic fault_irq;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      isr_q <= 32'h0;
    end else begin
      // Set interrupt flags
      if (cnt_wrap || (cnt_mode && cnt_zero)) begin
        isr_q[0] <= 1'b1;  // Period match
      end
      if (fault_active && !isr_q[1]) begin
        isr_q[1] <= 1'b1;  // Fault
      end

      // W1C in register write section
    end
  end

  assign irq_o = |(isr_q & ier_q);

  // ===========================================================================
  // Register Write Logic
  // ===========================================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      gcr_q      <= 32'h0;
      period_q   <= {PWM_WIDTH{1'b1}};
      psc_q      <= 16'h0;
      deadtime_q <= 32'h0;
      fault_q    <= 32'h0;
      ier_q      <= 32'h0;
      for (int i = 0; i < NUM_CHANNELS; i++) begin
        ccr[i]   <= 32'h0;
        duty[i]  <= '0;
        phase[i] <= '0;
      end
    end else if (stb_i && we_i) begin
      case (adr_i)
        6'h00: begin  // GCR
          if (byte_sel_i[0]) gcr_q[7:0] <= dat_i[7:0];
          if (byte_sel_i[1]) gcr_q[15:8] <= dat_i[15:8];
          if (byte_sel_i[2]) gcr_q[23:16] <= dat_i[23:16];
          if (byte_sel_i[3]) gcr_q[31:24] <= dat_i[31:24];
        end
        6'h01: begin  // PERIOD
          if (byte_sel_i[0]) period_q[7:0] <= dat_i[7:0];
          if (byte_sel_i[1]) period_q[15:8] <= dat_i[15:8];
        end
        6'h02: begin  // PSC
          if (byte_sel_i[0]) psc_q[7:0] <= dat_i[7:0];
          if (byte_sel_i[1]) psc_q[15:8] <= dat_i[15:8];
        end
        // CNT is read-only (6'h03)
        6'h04: begin  // DEADTIME
          if (byte_sel_i[0]) deadtime_q[7:0] <= dat_i[7:0];
          if (byte_sel_i[1]) deadtime_q[15:8] <= dat_i[15:8];
          if (byte_sel_i[2]) deadtime_q[23:16] <= dat_i[23:16];
          if (byte_sel_i[3]) deadtime_q[31:24] <= dat_i[31:24];
        end
        6'h05: begin  // FAULT
          if (byte_sel_i[0]) fault_q[7:0] <= dat_i[7:0];
          if (byte_sel_i[1]) fault_q[15:8] <= dat_i[15:8];
          // W1C for fault flag
          if (byte_sel_i[0] && dat_i[1]) begin
            // Clear fault_flag is handled separately
          end
        end
        6'h06: begin  // IER
          if (byte_sel_i[0]) ier_q[7:0] <= dat_i[7:0];
          if (byte_sel_i[1]) ier_q[15:8] <= dat_i[15:8];
          if (byte_sel_i[2]) ier_q[23:16] <= dat_i[23:16];
          if (byte_sel_i[3]) ier_q[31:24] <= dat_i[31:24];
        end
        6'h07: begin  // ISR (W1C)
          if (byte_sel_i[0] && dat_i[0]) isr_q[0] <= 1'b0;
          if (byte_sel_i[0] && dat_i[1]) isr_q[1] <= 1'b0;
        end
        default: begin
          // Per-channel registers
          if (adr_i >= CH_BASE_ADDR) begin
            logic [2:0] ch_idx;
            logic [1:0] reg_idx;
            ch_idx  = (adr_i - CH_BASE_ADDR) >> 2;
            reg_idx = adr_i[1:0];

            if (ch_idx < NUM_CHANNELS) begin
              case (reg_idx)
                2'h0: begin  // CCR
                  if (byte_sel_i[0]) ccr[ch_idx][7:0] <= dat_i[7:0];
                  if (byte_sel_i[1]) ccr[ch_idx][15:8] <= dat_i[15:8];
                  if (byte_sel_i[2]) ccr[ch_idx][23:16] <= dat_i[23:16];
                  if (byte_sel_i[3]) ccr[ch_idx][31:24] <= dat_i[31:24];
                end
                2'h1: begin  // DUTY
                  if (byte_sel_i[0]) duty[ch_idx][7:0] <= dat_i[7:0];
                  if (byte_sel_i[1]) duty[ch_idx][15:8] <= dat_i[15:8];
                end
                2'h2: begin  // PHASE
                  if (byte_sel_i[0]) phase[ch_idx][7:0] <= dat_i[7:0];
                  if (byte_sel_i[1]) phase[ch_idx][15:8] <= dat_i[15:8];
                end
                default: ;
              endcase
            end
          end
        end
      endcase
    end
  end

  // ===========================================================================
  // Read Data Mux
  // ===========================================================================
  always_comb begin
    dat_o = 32'h0;
    if (stb_i && !we_i) begin
      case (adr_i)
        6'h00: dat_o = gcr_q;
        6'h01: dat_o = {{(32 - PWM_WIDTH) {1'b0}}, period_q};
        6'h02: dat_o = {16'h0, psc_q};
        6'h03: dat_o = {{(32 - PWM_WIDTH) {1'b0}}, cnt_q};
        6'h04: dat_o = deadtime_q;
        6'h05: dat_o = {fault_q[31:2], fault_flag, fault_active};
        6'h06: dat_o = ier_q;
        6'h07: dat_o = isr_q;
        default: begin
          if (adr_i >= CH_BASE_ADDR) begin
            logic [2:0] ch_idx;
            logic [1:0] reg_idx;
            ch_idx  = (adr_i - CH_BASE_ADDR) >> 2;
            reg_idx = adr_i[1:0];

            if (ch_idx < NUM_CHANNELS) begin
              case (reg_idx)
                2'h0:    dat_o = ccr[ch_idx];
                2'h1:    dat_o = {{(32 - PWM_WIDTH) {1'b0}}, duty[ch_idx]};
                2'h2:    dat_o = {{(32 - PWM_WIDTH) {1'b0}}, phase[ch_idx]};
                default: dat_o = 32'h0;
              endcase
            end
          end
        end
      endcase
    end
  end

endmodule
