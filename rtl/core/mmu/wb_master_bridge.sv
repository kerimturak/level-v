/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

Description:
  Wishbone B4 Master Bridge
  
  Converts internal iomem interface to Wishbone B4 pipelined interface.
  Supports both single-beat transfers (uncached) and burst transfers (cache line).
  
  Features:
  - Single word transfers for uncached peripheral access
  - 4-beat incrementing burst for cache line fills (128-bit = 4 x 32-bit)
  - Pipelined interface with stall support
  - Error handling with retry support
*/

`timescale 1ns / 1ps
`include "ceres_defines.svh"
import ceres_param::*;

module wb_master_bridge (
    input logic clk_i,
    input logic rst_ni,

    // Internal iomem interface (from memory_arbiter)
    input  iomem_req_t iomem_req_i,
    output iomem_res_t iomem_res_o,

    // Wishbone B4 Master interface
    output wb_master_t wb_m_o,
    input  wb_slave_t  wb_s_i
);

  // ============================================================================
  // Local Parameters
  // ============================================================================
  localparam BURST_LEN = BLK_SIZE / WB_DATA_WIDTH;  // 128/32 = 4 beats
  localparam BEAT_CNT_W = $clog2(BURST_LEN);

  // ============================================================================
  // State Machine
  // ============================================================================
  typedef enum logic [2:0] {
    IDLE,
    SINGLE_REQ,   // Single word transfer (uncached)
    SINGLE_WAIT,  // Wait for single ack
    BURST_REQ,    // Burst request phase
    BURST_DATA,   // Burst data phase
    ERROR_HANDLE  // Error handling
  } state_e;

  state_e state_q, state_d;

  // ============================================================================
  // Registers
  // ============================================================================
  logic [WB_ADDR_WIDTH-1:0]                    addr_q;
  logic [    BURST_LEN-1:0][WB_DATA_WIDTH-1:0] wdata_q;  // Write data buffer
  logic [    BURST_LEN-1:0][WB_DATA_WIDTH-1:0] rdata_q;  // Read data buffer
  logic [     BEAT_CNT_W:0]                    beat_cnt_q;  // Beat counter (extra bit for overflow)
  logic [ WB_SEL_WIDTH-1:0]                    byte_sel_q;  // Byte select for single transfers
  logic                                        write_q;  // Write operation flag
  logic                                        uncached_q;  // Uncached access flag

  // ============================================================================
  // Combinational Logic
  // ============================================================================
  logic                                        is_write;
  logic                                        is_uncached;
  logic [    BURST_LEN-1:0][WB_DATA_WIDTH-1:0] wdata_packed;

  // Pack input data into burst format
  always_comb begin
    for (int i = 0; i < BURST_LEN; i++) begin
      wdata_packed[i] = iomem_req_i.data[i*WB_DATA_WIDTH+:WB_DATA_WIDTH];
    end
  end

  // Determine if this is a write and uncached access
  assign is_write = |iomem_req_i.rw;

  // Uncached detection: 
  // - For writes: check if all 16 bytes are enabled (cache line write has all 16 bits set)
  // - For reads: check if address is NOT cache-line aligned (lower 4 bits != 0)
  assign is_uncached = is_write ? ($countones(iomem_req_i.rw) < 16) : (iomem_req_i.addr[3:0] != 4'h0);

  // ============================================================================
  // State Machine
  // ============================================================================
  always_comb begin
    state_d = state_q;

    case (state_q)
      IDLE: begin
        if (iomem_req_i.valid) begin
          if (is_uncached) begin
            // Check for immediate ACK (combinational path through interconnect)
            if (wb_s_i.ack) begin
              state_d = IDLE;  // Stay in IDLE, transaction completes immediately
`ifdef VERILATOR
              $display("[%0t] WB_MASTER: IDLE_IMMEDIATE addr=%h write=%b rw=%h sel=%b", $time, iomem_req_i.addr, is_write, iomem_req_i.rw, byte_sel_comb);
`endif
            end else begin
              state_d = SINGLE_REQ;
            end
          end else begin
            state_d = BURST_REQ;
          end
        end
      end

      SINGLE_REQ: begin
        if (!wb_s_i.stall) begin
          // Check for immediate ACK (combinational slave like PBUS)
          if (wb_s_i.ack) begin
            state_d = IDLE;  // Direct completion
`ifdef VERILATOR
            $display("[%0t] WB_MASTER: SINGLE_IMMEDIATE addr=%h write=%b", $time, addr_q, write_q);
`endif
          end else begin
            state_d = SINGLE_WAIT;
`ifdef VERILATOR
            $display("[%0t] WB_MASTER: SINGLE_REQ->WAIT addr=%h stall=%b", $time, addr_q, wb_s_i.stall);
`endif
          end
        end
      end

      SINGLE_WAIT: begin
        if (wb_s_i.ack) begin
          state_d = IDLE;
`ifdef VERILATOR
          $display("[%0t] WB_MASTER: SINGLE_COMPLETE addr=%h write=%b ack=%b", $time, addr_q, write_q, wb_s_i.ack);
`endif
        end else if (wb_s_i.err) begin
          state_d = ERROR_HANDLE;
        end else if (wb_s_i.rty) begin
          state_d = SINGLE_REQ;  // Retry
        end
      end

      BURST_REQ: begin
        if (!wb_s_i.stall) begin
          state_d = BURST_DATA;
        end
      end

      BURST_DATA: begin
        if (wb_s_i.ack) begin
          if (beat_cnt_q == BURST_LEN - 1) begin
            state_d = IDLE;  // Burst complete
          end
        end else if (wb_s_i.err) begin
          state_d = ERROR_HANDLE;
        end
      end

      ERROR_HANDLE: begin
        // Simple error handling: return to idle
        state_d = IDLE;
      end

      default: state_d = IDLE;
    endcase
  end

  // ============================================================================
  // Sequential Logic
  // ============================================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q    <= IDLE;
      addr_q     <= '0;
      wdata_q    <= '0;
      rdata_q    <= '0;
      beat_cnt_q <= '0;
      byte_sel_q <= '0;
      write_q    <= 1'b0;
      uncached_q <= 1'b0;
    end else begin
      state_q <= state_d;

      case (state_q)
        IDLE: begin
          if (iomem_req_i.valid) begin
            addr_q     <= iomem_req_i.addr;
            wdata_q    <= wdata_packed;
            beat_cnt_q <= '0;
            write_q    <= is_write;
            uncached_q <= is_uncached;
`ifdef VERILATOR
            $display("[%0t] WB_MASTER: NEW_REQ addr=%h uncached=%b write=%b", $time, iomem_req_i.addr, is_uncached, is_write);
`endif

            // Extract byte select for uncached writes based on word offset
            if (is_uncached && is_write) begin
              byte_sel_q <= byte_sel_comb;
            end else begin
              byte_sel_q <= '1;  // Full word
            end
          end
        end

        SINGLE_WAIT: begin
          if (wb_s_i.ack && !write_q) begin
            // Store read data (replicate to all positions for simplicity)
            for (int i = 0; i < BURST_LEN; i++) begin
              rdata_q[i] <= wb_s_i.dat;
            end
          end
        end

        BURST_DATA: begin
          if (wb_s_i.ack) begin
            beat_cnt_q <= beat_cnt_q + 1;
            if (!write_q) begin
              rdata_q[beat_cnt_q[BEAT_CNT_W-1:0]] <= wb_s_i.dat;
`ifdef VERILATOR
              $display("[%0t] WB_MASTER: BURST_DATA beat=%0d addr=%h dat=%h", $time, beat_cnt_q, wb_m_o.adr, wb_s_i.dat);
`endif
            end
          end
        end

        default: ;
      endcase
    end
  end

  // ============================================================================
  // Wishbone Output Signals
  // ============================================================================
  // Combinational byte select for immediate use in SINGLE_REQ
  // Extract correct 4-bit byte select based on word offset within cache line
  logic [WB_SEL_WIDTH-1:0] byte_sel_comb;
  logic [             1:0] word_offset;
  assign word_offset = iomem_req_i.addr[3:2];  // Which word within 16-byte cache line

  always_comb begin
    case (word_offset)
      2'b00: byte_sel_comb = iomem_req_i.rw[3:0];
      2'b01: byte_sel_comb = iomem_req_i.rw[7:4];
      2'b10: byte_sel_comb = iomem_req_i.rw[11:8];
      2'b11: byte_sel_comb = iomem_req_i.rw[15:12];
    endcase
  end

  always_comb begin
    // Default values
    wb_m_o.adr = addr_q;
    wb_m_o.dat = wdata_q[beat_cnt_q[BEAT_CNT_W-1:0]];
    wb_m_o.sel = byte_sel_q;
    wb_m_o.we  = write_q;
    wb_m_o.stb = 1'b0;
    wb_m_o.cyc = 1'b0;
    wb_m_o.cti = WB_CTI_CLASSIC;
    wb_m_o.bte = WB_BTE_LINEAR;

    case (state_q)
      IDLE: begin
        // For immediate transition to SINGLE_REQ, prepare outputs
        if (iomem_req_i.valid && is_uncached) begin
          wb_m_o.cyc = 1'b1;
          wb_m_o.stb = 1'b1;
          wb_m_o.adr = iomem_req_i.addr;
          wb_m_o.we  = is_write;
          wb_m_o.sel = byte_sel_comb;
          wb_m_o.dat = iomem_req_i.data[31:0];
        end
      end

      SINGLE_REQ, SINGLE_WAIT: begin
        wb_m_o.cyc = 1'b1;
        wb_m_o.stb = (state_q == SINGLE_REQ);
        wb_m_o.cti = WB_CTI_CLASSIC;
        // Use registered byte select (set in previous cycle)
        wb_m_o.sel = byte_sel_q;
        // For single transfers that started this cycle, byte_sel_q may not be valid yet
        // So also update in IDLE case above
      end

      BURST_REQ, BURST_DATA: begin
        wb_m_o.cyc = 1'b1;
        wb_m_o.stb = 1'b1;
        wb_m_o.sel = '1;  // Full word for burst

        // Calculate burst address
        wb_m_o.adr = {addr_q[WB_ADDR_WIDTH-1:$clog2(BLK_SIZE/8)], beat_cnt_q[BEAT_CNT_W-1:0], 2'b00};

        // Set CTI based on position in burst
        if (beat_cnt_q == BURST_LEN - 1) begin
          wb_m_o.cti = WB_CTI_EOB;
        end else begin
          wb_m_o.cti = WB_CTI_INCR;
        end
        wb_m_o.bte = WB_BTE_WRAP4;  // 4-beat wrap for cache line
      end

      default: ;
    endcase
  end

  // ============================================================================
  // iomem Response Signals
  // ============================================================================
  always_comb begin
    iomem_res_o.valid = 1'b0;
    iomem_res_o.ready = (state_q == IDLE);
    iomem_res_o.data  = '0;

    // Pack read data back to cache line format
    // For last beat, use current wb_s_i.dat directly since rdata_q not yet updated
    for (int i = 0; i < BURST_LEN; i++) begin
      if (state_q == BURST_DATA && wb_s_i.ack && beat_cnt_q[BEAT_CNT_W-1:0] == i[BEAT_CNT_W-1:0]) begin
        // Last beat - use incoming data directly
        iomem_res_o.data[i*WB_DATA_WIDTH+:WB_DATA_WIDTH] = wb_s_i.dat;
      end else begin
        iomem_res_o.data[i*WB_DATA_WIDTH+:WB_DATA_WIDTH] = rdata_q[i];
      end
    end

    // Signal completion
    case (state_q)
      IDLE: begin
        // Immediate completion for fast uncached slaves (combinational ACK in same cycle)
        if (iomem_req_i.valid && is_uncached && wb_s_i.ack) begin
          iomem_res_o.valid = 1'b1;
          // For reads, use incoming data directly
          if (!is_write) begin
            for (int i = 0; i < BURST_LEN; i++) begin
              iomem_res_o.data[i*WB_DATA_WIDTH+:WB_DATA_WIDTH] = wb_s_i.dat;
            end
          end
        end
      end

      SINGLE_REQ: begin
        // Immediate ACK for fast slaves (like PBUS)
        iomem_res_o.valid = !wb_s_i.stall && wb_s_i.ack;
        // For reads, use incoming data directly
        if (!write_q) begin
          for (int i = 0; i < BURST_LEN; i++) begin
            iomem_res_o.data[i*WB_DATA_WIDTH+:WB_DATA_WIDTH] = wb_s_i.dat;
          end
        end
      end

      SINGLE_WAIT: begin
        iomem_res_o.valid = wb_s_i.ack;
      end

      BURST_DATA: begin
        iomem_res_o.valid = wb_s_i.ack && (beat_cnt_q == BURST_LEN - 1);
      end

      ERROR_HANDLE: begin
        // Signal completion even on error
        iomem_res_o.valid = 1'b1;
      end

      default: ;
    endcase
  end

`ifdef VERILATOR
  always_ff @(posedge clk_i) begin
    if (iomem_res_o.valid && !write_q) begin
      $display("[%0t] WB_MASTER: COMPLETE addr=%h data[0]=%h [1]=%h [2]=%h [3]=%h", $time, addr_q, iomem_res_o.data[31:0], iomem_res_o.data[63:32], iomem_res_o.data[95:64], iomem_res_o.data[127:96]);
    end
  end
`endif

endmodule
