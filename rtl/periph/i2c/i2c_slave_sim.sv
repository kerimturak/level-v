/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  Simple I2C Slave for Simulation Testing
  Implements a basic EEPROM-like memory (256 bytes)
  
  Features:
  - 7-bit slave address (configurable)
  - Single-byte memory address
  - Read/Write operations
  - Auto-increment address
  - Simulated ACK/NACK
*/
`timescale 1ns / 1ps

module i2c_slave_sim #(
    parameter logic [6:0] SLAVE_ADDR = 7'h50,
    parameter int         MEM_SIZE   = 256
) (
    input logic clk_i,
    input logic rst_ni,

    // I2C Interface
    input  logic scl_i,
    input  logic sda_i,
    output logic sda_o,
    output logic sda_oe_o
);

  // ============================================================================
  // State Machine
  // ============================================================================
  typedef enum logic [3:0] {
    IDLE,
    GET_ADDR,
    SEND_ADDR_ACK,
    GET_MEM_ADDR,
    SEND_MEM_ACK,
    GET_DATA,
    SEND_DATA_ACK,
    SEND_DATA,
    GET_DATA_ACK,
    WAIT_STOP
  } state_t;

  state_t       state_q;

  // ============================================================================
  // Internal Signals
  // ============================================================================
  logic   [7:0] mem        [0:MEM_SIZE-1];
  logic   [7:0] shift_reg;
  logic   [2:0] bit_cnt;
  logic   [7:0] mem_addr;
  logic         is_read;
  logic         scl_prev;
  logic         sda_prev;
  logic         scl_rise;
  logic         scl_fall;
  logic         start_cond;
  logic         stop_cond;
  logic         addr_match;

  // Edge detection
  always_ff @(posedge clk_i) begin
    scl_prev <= scl_i;
    sda_prev <= sda_i;
  end

  assign scl_rise   = scl_i && !scl_prev;
  assign scl_fall   = !scl_i && scl_prev;

  // START: SDA falls while SCL high
  assign start_cond = !sda_i && sda_prev && scl_i;

  // STOP: SDA rises while SCL high  
  assign stop_cond  = sda_i && !sda_prev && scl_i;

  // Address match check
  assign addr_match = (shift_reg[7:1] == SLAVE_ADDR);

  // ============================================================================
  // State Machine
  // ============================================================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      state_q   <= IDLE;
      shift_reg <= 8'b0;
      bit_cnt   <= 3'd0;
      mem_addr  <= 8'b0;
      is_read   <= 1'b0;
      sda_o     <= 1'b1;
      sda_oe_o  <= 1'b0;

      // Initialize memory with test pattern
      for (int i = 0; i < MEM_SIZE; i++) begin
        mem[i] <= 8'hFF;
      end
    end else begin
      // Default: release SDA
      sda_oe_o <= 1'b0;
      sda_o    <= 1'b1;

      // Handle START condition (can happen in any state)
      if (start_cond) begin
        state_q   <= GET_ADDR;
        bit_cnt   <= 3'd7;
        shift_reg <= 8'b0;
`ifdef VERILATOR
        $display("[I2C_SLAVE] START condition detected at time %0t", $time);
`endif
      end  // Handle STOP condition
      else if (stop_cond) begin
        state_q <= IDLE;
      end else begin
        case (state_q)
          IDLE: begin
            // Wait for START
          end

          GET_ADDR: begin
            if (scl_rise) begin
              shift_reg <= {shift_reg[6:0], sda_i};
`ifdef VERILATOR
              $display("[I2C_SLAVE] GET_ADDR: bit_cnt=%d, sda_i=%b, shift_reg=%02x", bit_cnt, sda_i, {shift_reg[6:0], sda_i});
`endif
              if (bit_cnt == 3'd0) begin
                state_q <= SEND_ADDR_ACK;
              end else begin
                bit_cnt <= bit_cnt - 1'b1;
              end
            end
          end

          SEND_ADDR_ACK: begin
            // Drive ACK low if address matches
            sda_oe_o <= 1'b1;
            sda_o    <= !addr_match;  // ACK = low

`ifdef VERILATOR
            if (scl_rise) begin
              $display("[I2C_SLAVE] SEND_ADDR_ACK: shift_reg=%02x, addr_match=%b", shift_reg, addr_match);
            end
`endif

            if (scl_fall) begin
              is_read <= shift_reg[0];  // R/W bit
              if (addr_match) begin
                if (shift_reg[0]) begin
                  // Read mode - send data
                  state_q   <= SEND_DATA;
                  shift_reg <= mem[mem_addr];
                  bit_cnt   <= 3'd7;
                end else begin
                  // Write mode - get memory address
                  state_q <= GET_MEM_ADDR;
                  bit_cnt <= 3'd7;
                end
              end else begin
                state_q <= IDLE;
              end
            end
          end

          GET_MEM_ADDR: begin
            if (scl_rise) begin
              shift_reg <= {shift_reg[6:0], sda_i};
              if (bit_cnt == 3'd0) begin
                state_q <= SEND_MEM_ACK;
              end else begin
                bit_cnt <= bit_cnt - 1'b1;
              end
            end
          end

          SEND_MEM_ACK: begin
            sda_oe_o <= 1'b1;
            sda_o    <= 1'b0;  // ACK

            if (scl_fall) begin
              mem_addr <= shift_reg;
              state_q  <= GET_DATA;
              bit_cnt  <= 3'd7;
            end
          end

          GET_DATA: begin
            if (scl_rise) begin
              shift_reg <= {shift_reg[6:0], sda_i};
              if (bit_cnt == 3'd0) begin
                state_q <= SEND_DATA_ACK;
              end else begin
                bit_cnt <= bit_cnt - 1'b1;
              end
            end
          end

          SEND_DATA_ACK: begin
            sda_oe_o <= 1'b1;
            sda_o    <= 1'b0;  // ACK

            if (scl_fall) begin
              // Store data
              mem[mem_addr] <= shift_reg;
              mem_addr      <= mem_addr + 1'b1;
              state_q       <= GET_DATA;
              bit_cnt       <= 3'd7;
            end
          end

          SEND_DATA: begin
            sda_oe_o <= 1'b1;
            sda_o    <= shift_reg[7];  // MSB first

            if (scl_fall) begin
              shift_reg <= {shift_reg[6:0], 1'b0};
              if (bit_cnt == 3'd0) begin
                state_q <= GET_DATA_ACK;
              end else begin
                bit_cnt <= bit_cnt - 1'b1;
              end
            end
          end

          GET_DATA_ACK: begin
            // Wait for master ACK/NACK
            if (scl_rise) begin
              if (sda_i) begin
                // NACK - stop sending
                state_q <= WAIT_STOP;
              end else begin
                // ACK - send next byte
                mem_addr  <= mem_addr + 1'b1;
                shift_reg <= mem[mem_addr+1'b1];
                bit_cnt   <= 3'd7;
                state_q   <= SEND_DATA;
              end
            end
          end

          WAIT_STOP: begin
            // Wait for STOP or repeated START
          end

          default: state_q <= IDLE;
        endcase
      end
    end
  end

endmodule
