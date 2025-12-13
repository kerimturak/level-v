/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  SPI Master Peripheral - Simple 8-bit SPI with FIFO
  
  Register Map (offset from base 0x2001_0000):
    0x00 - CTRL:   [31:16] sck_div, [3] cpol, [2] cpha, [1] cs_n, [0] spi_en
    0x04 - STATUS: [3] tx_empty, [2] tx_full, [1] rx_empty, [0] rx_full  (read-only)
    0x08 - RDATA:  [7:0] rx_data (read pops from RX FIFO)
    0x0C - WDATA:  [7:0] tx_data (write pushes to TX FIFO)
*/
`timescale 1ns / 1ps
module spi_master
  import ceres_param::*;
(
    input logic clk_i,
    input logic rst_ni,

    // Register interface (PBUS)
    input  logic            stb_i,
    input  logic [     1:0] adr_i,       // 2-bit address for 4 registers
    input  logic [     3:0] byte_sel_i,
    input  logic            we_i,
    input  logic [XLEN-1:0] dat_i,
    output logic [XLEN-1:0] dat_o,

    // SPI Interface
    output logic spi_sck_o,
    output logic spi_mosi_o,
    input  logic spi_miso_i,
    output logic spi_cs_n_o
);

  // ============================================================================
  // Control Register
  // ============================================================================
  logic [15:0] sck_div;  // Clock divider
  logic        cpol;  // Clock polarity
  logic        cpha;  // Clock phase
  logic        cs_n_reg;  // Chip select (directly controlled)
  logic        spi_en;  // SPI enable

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
  // SPI Engine State
  // ============================================================================
  typedef enum logic [1:0] {
    SPI_IDLE,
    SPI_TRANSFER,
    SPI_DONE
  } spi_state_t;

  spi_state_t state_q, state_d;
  logic [15:0] clk_cnt_q;
  logic [ 2:0] bit_cnt_q;
  logic [ 7:0] shift_out_q;
  logic [ 7:0] shift_in_q;
  logic        sck_q;
  logic        sck_toggle;

  // ============================================================================
  // TX FIFO
  // ============================================================================
  wbit_fifo #(
      .DATA_WIDTH(8),
      .FIFO_DEPTH(8)
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
  // RX FIFO
  // ============================================================================
  wbit_fifo #(
      .DATA_WIDTH(8),
      .FIFO_DEPTH(8)
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
  // Register Interface
  // ============================================================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      sck_div  <= 16'd100;  // Default divider
      cpol     <= 1'b0;
      cpha     <= 1'b0;
      cs_n_reg <= 1'b1;  // CS inactive (high)
      spi_en   <= 1'b0;
    end else if (stb_i && we_i && adr_i == 2'b00) begin
      // CTRL register write
      if (byte_sel_i[0]) begin
        spi_en   <= dat_i[0];
        cs_n_reg <= dat_i[1];
        cpha     <= dat_i[2];
        cpol     <= dat_i[3];
      end
      if (&byte_sel_i[3:2]) begin
        sck_div <= dat_i[31:16];
      end
    end
  end

  // Register read logic
  always_comb begin
    tx_we = 1'b0;
    rx_re = 1'b0;
    tx_wdata = dat_i[7:0];

    case (adr_i)
      2'b00: dat_o = {sck_div, 12'b0, cpol, cpha, cs_n_reg, spi_en};  // CTRL
      2'b01: dat_o = {28'b0, tx_empty, tx_full, rx_empty, rx_full};  // STATUS
      2'b10: begin
        dat_o = {24'b0, rx_rdata};  // RDATA
        rx_re = stb_i && !we_i && !rx_empty && byte_sel_i[0];
      end
      2'b11: begin
        dat_o = 32'b0;  // WDATA (write-only)
        tx_we = stb_i && we_i && !tx_full && byte_sel_i[0];
      end
    endcase
  end

`ifdef WB_INTC
  // Debug: SPI register access
  always_ff @(posedge clk_i) begin
    if (stb_i) begin
      $display("[%0t] SPI: stb=%b we=%b adr=%b dat_i=%h dat_o=%h tx_empty=%b tx_full=%b rx_empty=%b rx_full=%b", $time, stb_i, we_i, adr_i, dat_i, dat_o, tx_empty, tx_full, rx_empty, rx_full);
    end
  end
`endif

  // ============================================================================
  // SPI Clock Toggle Detection
  // ============================================================================
  assign sck_toggle = (clk_cnt_q == sck_div);

  // ============================================================================
  // SPI State Machine
  // ============================================================================
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      state_q     <= SPI_IDLE;
      clk_cnt_q   <= '0;
      bit_cnt_q   <= '0;
      shift_out_q <= '0;
      shift_in_q  <= '0;
      sck_q       <= 1'b0;
    end else begin
      state_q <= state_d;

      case (state_q)
        SPI_IDLE: begin
          sck_q     <= cpol;  // Idle clock level
          clk_cnt_q <= '0;
          bit_cnt_q <= '0;
          if (spi_en && !tx_empty && !cs_n_reg) begin
            shift_out_q <= tx_rdata;  // Load TX data
          end
        end

        SPI_TRANSFER: begin
          if (sck_toggle) begin
            clk_cnt_q <= '0;
            sck_q     <= ~sck_q;  // Toggle clock

            // Sample on one edge, shift on the other based on CPHA
            if (cpha == 1'b0) begin
              // Mode 0/2: Sample on first edge (rising for cpol=0), shift on second
              if (sck_q == cpol) begin
                // First edge - sample
                shift_in_q <= {shift_in_q[6:0], spi_miso_i};
              end else begin
                // Second edge - shift
                shift_out_q <= {shift_out_q[6:0], 1'b0};
                bit_cnt_q   <= bit_cnt_q + 1'b1;
              end
            end else begin
              // Mode 1/3: Shift on first edge, sample on second
              if (sck_q == cpol) begin
                // First edge - shift
                shift_out_q <= {shift_out_q[6:0], 1'b0};
              end else begin
                // Second edge - sample
                shift_in_q <= {shift_in_q[6:0], spi_miso_i};
                bit_cnt_q  <= bit_cnt_q + 1'b1;
              end
            end
          end else begin
            clk_cnt_q <= clk_cnt_q + 1'b1;
          end
        end

        SPI_DONE: begin
          sck_q <= cpol;  // Return to idle level
        end
      endcase
    end
  end

  // State transition logic
  always_comb begin
    state_d  = state_q;
    tx_re    = 1'b0;
    rx_we    = 1'b0;
    rx_wdata = shift_in_q;

    case (state_q)
      SPI_IDLE: begin
        if (spi_en && !tx_empty && !cs_n_reg) begin
          state_d = SPI_TRANSFER;
          tx_re   = 1'b1;  // Pop from TX FIFO
        end
      end

      SPI_TRANSFER: begin
        if (bit_cnt_q == 3'd7 && sck_toggle && ((cpha == 1'b0 && sck_q != cpol) || (cpha == 1'b1 && sck_q != cpol))) begin
          state_d = SPI_DONE;
        end
      end

      SPI_DONE: begin
        rx_we = !rx_full;  // Push to RX FIFO
        if (!tx_empty && !cs_n_reg) begin
          state_d = SPI_TRANSFER;
          tx_re   = 1'b1;
        end else begin
          state_d = SPI_IDLE;
        end
      end
    endcase
  end

  // ============================================================================
  // Output Assignments
  // ============================================================================
  assign spi_sck_o  = sck_q;
  assign spi_mosi_o = shift_out_q[7];  // MSB first
  assign spi_cs_n_o = cs_n_reg;

endmodule
