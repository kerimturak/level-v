/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  I2C Master Peripheral with FIFO buffers
  Supports Standard (100kHz), Fast (400kHz), and Fast+ (1MHz) modes
  
  Register Map (offset from base):
    0x00 - CTRL:    [31:16] clk_div, [3] stretch_en, [2] ack_en
    0x04 - STATUS:  [7] busy, [6] arb_lost, [5] ack_err, [4] tx_empty, 
                    [3] tx_full, [2] rx_empty, [1] rx_full, [0] transfer_done
    0x08 - CMD:     [7] start, [6] stop, [5] read, [4] write, [3] ack
    0x0C - ADDR:    [7:1] slave_addr, [0] r/w bit
    0x10 - RDATA:   [7:0] rx_data (read pops from RX FIFO)
    0x14 - WDATA:   [7:0] tx_data (write pushes to TX FIFO)
  
  I2C Timing (for clk_div calculation):
    SCL frequency = clk_i / (4 * (clk_div + 1))
    Example: 50MHz / (4 * 125) = 100kHz (Standard mode)
             50MHz / (4 * 31)  = 400kHz (Fast mode)
*/
`timescale 1ns / 1ps

module i2c_master
  import ceres_param::*;
(
    input logic clk_i,
    input logic rst_ni,

    // Register interface (PBUS style)
    input  logic            stb_i,
    input  logic [     2:0] adr_i,       // 3-bit address for 6 registers
    input  logic [     3:0] byte_sel_i,
    input  logic            we_i,
    input  logic [XLEN-1:0] dat_i,
    output logic [XLEN-1:0] dat_o,

    // I2C Interface (needs external tri-state)
    output logic i2c_scl_o,     // SCL output
    output logic i2c_scl_oe_o,  // SCL output enable (active high)
    input  logic i2c_scl_i,     // SCL input (for clock stretching)
    output logic i2c_sda_o,     // SDA output
    output logic i2c_sda_oe_o,  // SDA output enable (active high)
    input  logic i2c_sda_i,     // SDA input

    // Interrupt
    output logic irq_o
);

  // ============================================================================
  // Parameters
  // ============================================================================
  localparam int FIFO_DEPTH = 8;

  // ============================================================================
  // Control Register
  // ============================================================================
  logic [15:0] clk_div;  // SCL clock divider
  logic        stretch_en;  // Clock stretching enable
  logic        ack_en;  // Auto ACK enable for reads

  // ============================================================================
  // Status Register
  // ============================================================================
  logic        busy;
  logic        arb_lost;  // Arbitration lost (sticky, clear on read)
  logic        ack_err;  // No ACK received when expected (sticky, clear on read)
  logic        transfer_done;  // Byte transfer complete (sticky, clear on read)

  // ============================================================================
  // Command Register
  // ============================================================================
  logic        cmd_start;  // Generate START condition
  logic        cmd_stop;  // Generate STOP condition
  logic        cmd_read;  // Read byte
  logic        cmd_write;  // Write byte
  logic        cmd_ack;  // ACK to send (0=ACK, 1=NACK)
  logic        cmd_pending;  // Command is pending

  // ============================================================================
  // TX FIFO Signals
  // ============================================================================
  logic        tx_we;
  logic        tx_re;
  logic [ 7:0] tx_wdata;
  logic [ 7:0] tx_rdata;
  logic        tx_full;
  logic        tx_empty;

  // ============================================================================
  // RX FIFO Signals
  // ============================================================================
  logic        rx_we;
  logic        rx_re;
  logic [ 7:0] rx_wdata;
  logic [ 7:0] rx_rdata;
  logic        rx_full;
  logic        rx_empty;

  // ============================================================================
  // I2C Engine State Machine
  // ============================================================================
  typedef enum logic [3:0] {
    I2C_IDLE,
    I2C_START_1,       // SDA goes low while SCL high
    I2C_START_2,       // SCL goes low
    I2C_BIT_SETUP,     // Setup data on SDA
    I2C_BIT_SCL_HIGH,  // SCL goes high, sample/hold
    I2C_BIT_SCL_LOW,   // SCL goes low
    I2C_ACK_SETUP,     // Setup ACK on SDA
    I2C_ACK_SCL_HIGH,  // Sample ACK
    I2C_ACK_SCL_LOW,   // SCL goes low after ACK
    I2C_STOP_1,        // SCL goes high
    I2C_STOP_2,        // SDA goes high (STOP)
    I2C_STRETCH        // Wait for clock stretch release
  } i2c_state_t;

  i2c_state_t state_q, state_d;
  logic [15:0] clk_cnt_q;
  logic [ 2:0] bit_cnt_q;
  logic [ 7:0] shift_out_q;
  logic [ 7:0] shift_in_q;
  logic scl_q, sda_q;
  logic scl_oe_q, sda_oe_q;
  logic       is_read_q;

  // Next state signals for sequential assignment
  logic [2:0] bit_cnt_next;
  logic [7:0] shift_out_next;
  logic       is_read_next;
  logic       load_next_byte;
  logic       do_tx_re;

  // Clock divider tick
  logic       clk_tick;
  assign clk_tick = (clk_cnt_q == clk_div);

  // ============================================================================
  // TX FIFO Instance
  // ============================================================================
  wbit_fifo #(
      .DATA_WIDTH(8),
      .FIFO_DEPTH(FIFO_DEPTH)
  ) i_tx_fifo (
      .clk       (clk_i),
      .rst       (!rst_ni),
      .write_en  (tx_we),
      .read_en   (tx_re),
      .write_data(tx_wdata),
      .read_data (tx_rdata),
      .full      (tx_full),
      .empty     (tx_empty)
  );

  // ============================================================================
  // RX FIFO Instance
  // ============================================================================
  wbit_fifo #(
      .DATA_WIDTH(8),
      .FIFO_DEPTH(FIFO_DEPTH)
  ) i_rx_fifo (
      .clk       (clk_i),
      .rst       (!rst_ni),
      .write_en  (rx_we),
      .read_en   (rx_re),
      .write_data(rx_wdata),
      .read_data (rx_rdata),
      .full      (rx_full),
      .empty     (rx_empty)
  );

  // ============================================================================
  // Register Write Logic
  // ============================================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      clk_div     <= 16'd124;  // Default: 100kHz @ 50MHz
      stretch_en  <= 1'b1;
      ack_en      <= 1'b1;
      cmd_start   <= 1'b0;
      cmd_stop    <= 1'b0;
      cmd_read    <= 1'b0;
      cmd_write   <= 1'b0;
      cmd_ack     <= 1'b0;
      cmd_pending <= 1'b0;
    end else begin
      // Clear command bits when accepted by FSM
      if (state_q != I2C_IDLE && state_d == I2C_IDLE) begin
        cmd_pending <= 1'b0;
      end

      if (stb_i && we_i) begin
        case (adr_i)
          3'b000: begin  // CTRL
            if (byte_sel_i[0]) begin
              stretch_en <= dat_i[3];
              ack_en     <= dat_i[2];
            end
            if (&byte_sel_i[3:2]) begin
              clk_div <= dat_i[31:16];
            end
          end
          3'b010: begin  // CMD
            if (byte_sel_i[0]) begin
              cmd_start   <= dat_i[7];
              cmd_stop    <= dat_i[6];
              cmd_read    <= dat_i[5];
              cmd_write   <= dat_i[4];
              cmd_ack     <= dat_i[3];
              cmd_pending <= 1'b1;
            end
          end
          default: ;
        endcase
      end
    end
  end

  // ============================================================================
  // Register Read Logic
  // ============================================================================
  logic status_read;  // Status register being read

  always_comb begin
    tx_we       = 1'b0;
    tx_wdata    = 8'b0;
    rx_re       = 1'b0;
    status_read = 1'b0;

    case (adr_i)
      3'b000:  dat_o = {clk_div, 12'b0, stretch_en, ack_en, 2'b0};
      3'b001: begin
        dat_o = {24'b0, busy, arb_lost, ack_err, tx_empty, tx_full, rx_empty, rx_full, transfer_done};
        status_read = stb_i && !we_i;  // Clear sticky flags on read
      end
      3'b010:  dat_o = {24'b0, cmd_start, cmd_stop, cmd_read, cmd_write, cmd_ack, 3'b0};
      3'b011:  dat_o = 32'b0;  // ADDR (write-only for simplicity)
      3'b100: begin  // RDATA
        dat_o = {24'b0, rx_rdata};
        rx_re = stb_i && !we_i && !rx_empty && byte_sel_i[0];
      end
      3'b101: begin  // WDATA
        dat_o = 32'b0;
        if (stb_i && we_i && !tx_full && byte_sel_i[0]) begin
          tx_we    = 1'b1;
          tx_wdata = dat_i[7:0];
        end
      end
      3'b110: begin  // DEBUG: state machine state, cmd_pending, clk_cnt
        dat_o = {clk_cnt_q, 7'b0, cmd_pending, 4'b0, state_q};
      end
      default: dat_o = 32'b0;
    endcase
  end

  // ============================================================================
  // Next State Logic (pure combinational)
  // ============================================================================
  always_comb begin
    state_d        = state_q;
    do_tx_re       = 1'b0;
    bit_cnt_next   = bit_cnt_q;
    shift_out_next = shift_out_q;
    is_read_next   = is_read_q;
    load_next_byte = 1'b0;

    case (state_q)
      I2C_IDLE: begin
        if (cmd_pending && cmd_start && !tx_empty) begin
          do_tx_re = 1'b1;  // Read address byte from FIFO
          state_d  = I2C_START_1;
        end
      end

      I2C_START_1: begin
        // Wait one tick then go to START_2
        if (clk_tick) state_d = I2C_START_2;
      end

      I2C_START_2: begin
        // Wait one tick then go to BIT_SETUP
        if (clk_tick) state_d = I2C_BIT_SETUP;
      end

      I2C_BIT_SETUP: begin
        if (clk_tick) state_d = I2C_BIT_SCL_HIGH;
      end

      I2C_BIT_SCL_HIGH: begin
        // SCL goes high first, then check for stretch
        // Only check stretch after SCL has been released (scl_oe = 0)
        if (scl_oe_q == 1'b0 && stretch_en && !i2c_scl_i) begin
          state_d = I2C_STRETCH;
        end else if (clk_tick) begin
          state_d = I2C_BIT_SCL_LOW;
        end
        if (arb_lost) state_d = I2C_IDLE;
      end

      I2C_BIT_SCL_LOW: begin
        if (clk_tick) begin
          bit_cnt_next   = bit_cnt_q - 1'b1;
          shift_out_next = {shift_out_q[6:0], 1'b0};
          if (bit_cnt_q == 3'd0) begin
            state_d = I2C_ACK_SETUP;
          end else begin
            state_d = I2C_BIT_SETUP;
          end
        end
      end

      I2C_ACK_SETUP: begin
        if (clk_tick) state_d = I2C_ACK_SCL_HIGH;
      end

      I2C_ACK_SCL_HIGH: begin
        // Only check stretch after SCL has been released
        if (scl_oe_q == 1'b0 && stretch_en && !i2c_scl_i) begin
          state_d = I2C_STRETCH;
        end else if (clk_tick) begin
          state_d = I2C_ACK_SCL_LOW;
        end
      end

      I2C_ACK_SCL_LOW: begin
        if (clk_tick) begin
          if (cmd_stop || ack_err) begin
            state_d = I2C_STOP_1;
          end else if (cmd_read && !rx_full) begin
            is_read_next = 1'b1;
            bit_cnt_next = 3'd7;
            state_d      = I2C_BIT_SETUP;
          end else if (cmd_write && !tx_empty) begin
            do_tx_re       = 1'b1;
            load_next_byte = 1'b1;
            is_read_next   = 1'b0;
            bit_cnt_next   = 3'd7;
            state_d        = I2C_BIT_SETUP;
          end else begin
            state_d = I2C_STOP_1;
          end
        end
      end

      I2C_STOP_1: begin
        if (clk_tick) state_d = I2C_STOP_2;
      end

      I2C_STOP_2: begin
        if (clk_tick) state_d = I2C_IDLE;
      end

      I2C_STRETCH: begin
        if (i2c_scl_i) begin
          state_d = I2C_BIT_SCL_HIGH;
        end
      end

      default: state_d = I2C_IDLE;
    endcase
  end

  // TX FIFO read enable from combinational logic
  assign tx_re = do_tx_re;

  // ============================================================================
  // I2C State Machine (Sequential)
  // ============================================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q       <= I2C_IDLE;
      clk_cnt_q     <= 16'b0;
      bit_cnt_q     <= 3'b0;
      shift_out_q   <= 8'b0;
      shift_in_q    <= 8'b0;
      scl_q         <= 1'b1;
      sda_q         <= 1'b1;
      scl_oe_q      <= 1'b0;
      sda_oe_q      <= 1'b0;
      is_read_q     <= 1'b0;
      busy          <= 1'b0;
      arb_lost      <= 1'b0;
      ack_err       <= 1'b0;
      transfer_done <= 1'b0;
      rx_we         <= 1'b0;
      rx_wdata      <= 8'b0;
    end else begin
      state_q <= state_d;

      // Update from combinational logic
      bit_cnt_q <= bit_cnt_next;
      shift_out_q <= load_next_byte ? tx_rdata : shift_out_next;
      is_read_q <= is_read_next;

      // Clear sticky status flags when STATUS register is read
      if (status_read) begin
        transfer_done <= 1'b0;
        ack_err       <= 1'b0;
        arb_lost      <= 1'b0;
      end

      // RX FIFO write pulse clear
      if (rx_we) rx_we <= 1'b0;

      // Clock counter
      if (state_q == I2C_IDLE) begin
        clk_cnt_q <= 16'b0;
      end else if (clk_tick) begin
        clk_cnt_q <= 16'b0;
      end else begin
        clk_cnt_q <= clk_cnt_q + 1'b1;
      end

      case (state_q)
        I2C_IDLE: begin
          scl_q    <= 1'b1;
          sda_q    <= 1'b1;
          scl_oe_q <= 1'b0;
          sda_oe_q <= 1'b0;
          busy     <= 1'b0;

          if (cmd_pending && cmd_start && !tx_empty) begin
            busy      <= 1'b1;
            sda_oe_q  <= 1'b1;
            scl_oe_q  <= 1'b1;
            arb_lost  <= 1'b0;
            ack_err   <= 1'b0;
            bit_cnt_q <= 3'd7;
            // Note: tx_rdata will be valid next cycle after tx_re
          end
        end

        I2C_START_1: begin
          // Load address byte from FIFO (tx_re was set in previous cycle)
          shift_out_q <= tx_rdata;
          is_read_q   <= tx_rdata[0];  // R/W bit
          if (clk_tick) begin
            sda_q <= 1'b0;  // SDA low while SCL high (START condition)
          end
        end

        I2C_START_2: begin
          if (clk_tick) begin
            scl_q <= 1'b0;  // SCL goes low
          end
        end

        I2C_BIT_SETUP: begin
          if (clk_tick) begin
            if (is_read_q) begin
              sda_q    <= 1'b1;  // Release SDA for read
              sda_oe_q <= 1'b0;
            end else begin
              sda_q    <= shift_out_q[7];  // MSB first
              sda_oe_q <= 1'b1;
            end
          end
        end

        I2C_BIT_SCL_HIGH: begin
          // SCL goes high, sample SDA
          scl_q    <= 1'b1;
          scl_oe_q <= 1'b0;  // Release SCL for stretch

          if (clk_tick) begin
            // Sample on SCL high
            shift_in_q <= {shift_in_q[6:0], i2c_sda_i};

            // Arbitration check for writes
            if (!is_read_q && sda_oe_q && (sda_q != i2c_sda_i)) begin
              arb_lost <= 1'b1;
            end
          end
        end

        I2C_BIT_SCL_LOW: begin
          if (clk_tick) begin
            scl_q    <= 1'b0;
            scl_oe_q <= 1'b1;
          end
        end

        I2C_ACK_SETUP: begin
          if (clk_tick) begin
            if (is_read_q) begin
              // Master sends ACK/NACK
              sda_q    <= cmd_ack;  // 0=ACK, 1=NACK
              sda_oe_q <= 1'b1;
            end else begin
              // Release SDA to receive ACK from slave
              sda_q    <= 1'b1;
              sda_oe_q <= 1'b0;
            end
          end
        end

        I2C_ACK_SCL_HIGH: begin
          // SCL goes high, sample ACK
          scl_q    <= 1'b1;
          scl_oe_q <= 1'b0;

          if (clk_tick) begin
            // Check ACK for writes (slave should pull low)
            if (!is_read_q && i2c_sda_i) begin
              ack_err <= 1'b1;  // No ACK received
            end
          end
        end

        I2C_ACK_SCL_LOW: begin
          if (clk_tick) begin
            scl_q         <= 1'b0;
            scl_oe_q      <= 1'b1;
            transfer_done <= 1'b1;

            // Store received byte
            if (is_read_q && !rx_full) begin
              rx_we    <= 1'b1;
              rx_wdata <= shift_in_q;
            end
          end
        end

        I2C_STOP_1: begin
          // SDA low, then SCL high
          sda_q    <= 1'b0;
          sda_oe_q <= 1'b1;
          if (clk_tick) begin
            scl_q    <= 1'b1;
            scl_oe_q <= 1'b0;
          end
        end

        I2C_STOP_2: begin
          // SDA goes high (STOP condition)
          if (clk_tick) begin
            sda_q    <= 1'b1;
            sda_oe_q <= 1'b0;
          end
        end

        I2C_STRETCH: begin
          // Just wait
        end

        default: ;
      endcase
    end
  end

  // ============================================================================
  // Output Assignments
  // ============================================================================
  assign i2c_scl_o    = scl_q;
  assign i2c_scl_oe_o = scl_oe_q;
  assign i2c_sda_o    = sda_q;
  assign i2c_sda_oe_o = sda_oe_q;

  // Interrupt on transfer complete or error
  assign irq_o = transfer_done | ack_err | arb_lost;

endmodule
