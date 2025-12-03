/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

================================================================================
DMA Controller Module
================================================================================
Features:
  - 4 independent DMA channels
  - Memory-to-memory transfers
  - Peripheral-to-memory and memory-to-peripheral
  - Configurable burst sizes (1, 4, 8, 16 words)
  - Circular buffer mode
  - Half-transfer and transfer-complete interrupts
  - Channel priority levels
  - Source/destination increment modes
  - Word, half-word, and byte transfers

Channel Register Map (per channel, 0x20 bytes each):
  0x00: CCR    - Channel control register
  0x04: CNDTR  - Channel number of data to transfer
  0x08: CPAR   - Channel peripheral address
  0x0C: CMAR   - Channel memory address
  0x10: CTCNT  - Channel transfer count (current, read-only)

Global Register Map (at base):
  0x80: ISR    - Interrupt status register
  0x84: IFCR   - Interrupt flag clear register
  0x88: GCR    - Global control register

CCR Register [31:0]:
  [0]     : EN     - Channel enable
  [1]     : TCIE   - Transfer complete interrupt enable
  [2]     : HTIE   - Half transfer interrupt enable
  [3]     : TEIE   - Transfer error interrupt enable
  [4]     : DIR    - Direction (0=peripheral-to-memory, 1=memory-to-peripheral)
  [5]     : CIRC   - Circular mode
  [6]     : PINC   - Peripheral increment mode
  [7]     : MINC   - Memory increment mode
  [9:8]   : PSIZE  - Peripheral size (00=byte, 01=half-word, 10=word)
  [11:10] : MSIZE  - Memory size (00=byte, 01=half-word, 10=word)
  [13:12] : PL     - Priority level (00=low, 01=medium, 10=high, 11=very high)
  [14]    : MEM2MEM- Memory-to-memory mode
  [17:15] : BURST  - Burst size (000=1, 001=4, 010=8, 011=16)
  [31:18] : Reserved

ISR Register (read-only):
  Per channel (bits [3:0] for ch0, [7:4] for ch1, etc.):
  [0] : GIF  - Global interrupt flag
  [1] : TCIF - Transfer complete interrupt flag
  [2] : HTIF - Half transfer interrupt flag
  [3] : TEIF - Transfer error interrupt flag

================================================================================
*/

`timescale 1ns / 1ps

module dma
  import ceres_param::*;
#(
    parameter int NUM_CHANNELS = 4,
    parameter int MAX_BURST    = 16
) (
    input  logic                    clk_i,
    input  logic                    rst_ni,
    // Register Interface (slave)
    input  logic                    stb_i,
    input  logic [             5:0] adr_i,        // Word address [7:2]
    input  logic [             3:0] byte_sel_i,
    input  logic                    we_i,
    input  logic [            31:0] dat_i,
    output logic [            31:0] dat_o,
    // DMA Master Interface
    output logic                    dma_req_o,
    output logic [            31:0] dma_addr_o,
    output logic [            31:0] dma_wdata_o,
    output logic [             3:0] dma_wstrb_o,
    input  logic [            31:0] dma_rdata_i,
    input  logic                    dma_ack_i,
    // Peripheral DMA requests
    input  logic [NUM_CHANNELS-1:0] dreq_i,
    // Interrupt output
    output logic [NUM_CHANNELS-1:0] irq_o
);

  // ===========================================================================
  // Local Parameters
  // ===========================================================================
  localparam int CH_REG_SIZE = 8;  // 8 words per channel (0x20 bytes)

  // Size encodings
  localparam logic [1:0] SIZE_BYTE = 2'b00;
  localparam logic [1:0] SIZE_HALF = 2'b01;
  localparam logic [1:0] SIZE_WORD = 2'b10;

  // ===========================================================================
  // Per-Channel Registers
  // ===========================================================================
  logic [            31:0] ccr                        [NUM_CHANNELS];  // Control register
  logic [            31:0] cndtr                      [NUM_CHANNELS];  // Number of data to transfer
  logic [            31:0] cpar                       [NUM_CHANNELS];  // Peripheral address
  logic [            31:0] cmar                       [NUM_CHANNELS];  // Memory address
  logic [            31:0] ctcnt                      [NUM_CHANNELS];  // Current transfer count

  // Internal channel state
  logic [            31:0] cur_paddr                  [NUM_CHANNELS];  // Current peripheral address
  logic [            31:0] cur_maddr                  [NUM_CHANNELS];  // Current memory address

  // Global registers
  logic [            31:0] isr_q;  // Interrupt status
  logic [            31:0] gcr_q;  // Global control

  // ===========================================================================
  // Channel Control Bit Extraction
  // ===========================================================================
  logic [NUM_CHANNELS-1:0] ch_en;
  logic [NUM_CHANNELS-1:0] ch_tcie;
  logic [NUM_CHANNELS-1:0] ch_htie;
  logic [NUM_CHANNELS-1:0] ch_teie;
  logic [NUM_CHANNELS-1:0] ch_dir;
  logic [NUM_CHANNELS-1:0] ch_circ;
  logic [NUM_CHANNELS-1:0] ch_pinc;
  logic [NUM_CHANNELS-1:0] ch_minc;
  logic [             1:0] ch_psize                   [NUM_CHANNELS];
  logic [             1:0] ch_msize                   [NUM_CHANNELS];
  logic [             1:0] ch_pl                      [NUM_CHANNELS];
  logic [NUM_CHANNELS-1:0] ch_mem2mem;
  logic [             2:0] ch_burst                   [NUM_CHANNELS];

  generate
    for (genvar i = 0; i < NUM_CHANNELS; i++) begin : gen_ch_ctrl
      assign ch_en[i]      = ccr[i][0];
      assign ch_tcie[i]    = ccr[i][1];
      assign ch_htie[i]    = ccr[i][2];
      assign ch_teie[i]    = ccr[i][3];
      assign ch_dir[i]     = ccr[i][4];
      assign ch_circ[i]    = ccr[i][5];
      assign ch_pinc[i]    = ccr[i][6];
      assign ch_minc[i]    = ccr[i][7];
      assign ch_psize[i]   = ccr[i][9:8];
      assign ch_msize[i]   = ccr[i][11:10];
      assign ch_pl[i]      = ccr[i][13:12];
      assign ch_mem2mem[i] = ccr[i][14];
      assign ch_burst[i]   = ccr[i][17:15];
    end
  endgenerate

  // ===========================================================================
  // Interrupt Status Bits
  // ===========================================================================
  logic [NUM_CHANNELS-1:0] gif;  // Global interrupt flag
  logic [NUM_CHANNELS-1:0] tcif;  // Transfer complete
  logic [NUM_CHANNELS-1:0] htif;  // Half transfer
  logic [NUM_CHANNELS-1:0] teif;  // Transfer error

  always_comb begin
    isr_q = 32'h0;
    for (int i = 0; i < NUM_CHANNELS; i++) begin
      isr_q[i*4+0] = gif[i];
      isr_q[i*4+1] = tcif[i];
      isr_q[i*4+2] = htif[i];
      isr_q[i*4+3] = teif[i];
    end
  end

  // ===========================================================================
  // DMA State Machine
  // ===========================================================================
  typedef enum logic [2:0] {
    DMA_IDLE,
    DMA_READ_REQ,
    DMA_READ_WAIT,
    DMA_WRITE_REQ,
    DMA_WRITE_WAIT,
    DMA_DONE
  } dma_state_t;

  dma_state_t state_q, state_d;

  // Active channel and transfer tracking
  logic [$clog2(NUM_CHANNELS)-1:0] active_ch;
  logic [                    31:0] xfer_data;
  logic [     $clog2(MAX_BURST):0] burst_cnt;
  logic                            active_ch_valid;

  // ===========================================================================
  // Channel Arbitration (Priority-based, round-robin within same priority)
  // ===========================================================================
  logic [        NUM_CHANNELS-1:0] ch_request;
  logic [        NUM_CHANNELS-1:0] ch_grant;

  // Request is valid if channel enabled and (has pending request or mem2mem)
  generate
    for (genvar i = 0; i < NUM_CHANNELS; i++) begin : gen_ch_req
      assign ch_request[i] = ch_en[i] & (ctcnt[i] > 0) & (ch_mem2mem[i] | dreq_i[i]);
    end
  endgenerate

  // Simple priority encoder (higher numbered priority wins)
  always_comb begin
    active_ch       = '0;
    active_ch_valid = 1'b0;
    ch_grant        = '0;

    // Find highest priority active channel
    for (int p = 3; p >= 0; p--) begin
      for (int i = 0; i < NUM_CHANNELS; i++) begin
        if (ch_request[i] && ch_pl[i] == p[1:0] && !active_ch_valid) begin
          active_ch       = i[$clog2(NUM_CHANNELS)-1:0];
          active_ch_valid = 1'b1;
          ch_grant[i]     = 1'b1;
        end
      end
    end
  end

  // ===========================================================================
  // Transfer Size Calculation
  // ===========================================================================
  function automatic logic [3:0] get_wstrb(input logic [1:0] size, input logic [1:0] addr_lsb);
    case (size)
      SIZE_BYTE: get_wstrb = 4'b0001 << addr_lsb;
      SIZE_HALF: get_wstrb = 4'b0011 << {addr_lsb[1], 1'b0};
      SIZE_WORD: get_wstrb = 4'b1111;
      default:   get_wstrb = 4'b1111;
    endcase
  endfunction

  function automatic logic [31:0] get_addr_inc(input logic [1:0] size);
    case (size)
      SIZE_BYTE: get_addr_inc = 32'd1;
      SIZE_HALF: get_addr_inc = 32'd2;
      SIZE_WORD: get_addr_inc = 32'd4;
      default:   get_addr_inc = 32'd4;
    endcase
  endfunction

  // ===========================================================================
  // DMA State Machine Logic
  // ===========================================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q   <= DMA_IDLE;
      xfer_data <= 32'h0;
      burst_cnt <= '0;
    end else begin
      state_q <= state_d;

      case (state_q)
        DMA_READ_WAIT: begin
          if (dma_ack_i) begin
            xfer_data <= dma_rdata_i;
          end
        end
        default: ;
      endcase
    end
  end

  always_comb begin
    state_d     = state_q;
    dma_req_o   = 1'b0;
    dma_addr_o  = 32'h0;
    dma_wdata_o = 32'h0;
    dma_wstrb_o = 4'h0;

    case (state_q)
      DMA_IDLE: begin
        if (active_ch_valid) begin
          state_d = DMA_READ_REQ;
        end
      end

      DMA_READ_REQ: begin
        dma_req_o = 1'b1;
        // Read from source (peripheral or memory)
        if (ch_dir[active_ch] || ch_mem2mem[active_ch]) begin
          dma_addr_o = cur_maddr[active_ch];
        end else begin
          dma_addr_o = cur_paddr[active_ch];
        end
        state_d = DMA_READ_WAIT;
      end

      DMA_READ_WAIT: begin
        dma_req_o = 1'b1;
        if (ch_dir[active_ch] || ch_mem2mem[active_ch]) begin
          dma_addr_o = cur_maddr[active_ch];
        end else begin
          dma_addr_o = cur_paddr[active_ch];
        end
        if (dma_ack_i) begin
          state_d = DMA_WRITE_REQ;
        end
      end

      DMA_WRITE_REQ: begin
        dma_req_o   = 1'b1;
        dma_wdata_o = xfer_data;
        // Write to destination
        if (ch_dir[active_ch]) begin
          dma_addr_o  = cur_paddr[active_ch];
          dma_wstrb_o = get_wstrb(ch_psize[active_ch], cur_paddr[active_ch][1:0]);
        end else begin
          dma_addr_o  = cur_maddr[active_ch];
          dma_wstrb_o = get_wstrb(ch_msize[active_ch], cur_maddr[active_ch][1:0]);
        end
        state_d = DMA_WRITE_WAIT;
      end

      DMA_WRITE_WAIT: begin
        dma_req_o   = 1'b1;
        dma_wdata_o = xfer_data;
        if (ch_dir[active_ch]) begin
          dma_addr_o  = cur_paddr[active_ch];
          dma_wstrb_o = get_wstrb(ch_psize[active_ch], cur_paddr[active_ch][1:0]);
        end else begin
          dma_addr_o  = cur_maddr[active_ch];
          dma_wstrb_o = get_wstrb(ch_msize[active_ch], cur_maddr[active_ch][1:0]);
        end
        if (dma_ack_i) begin
          state_d = DMA_DONE;
        end
      end

      DMA_DONE: begin
        state_d = DMA_IDLE;
      end

      default: state_d = DMA_IDLE;
    endcase
  end

  // ===========================================================================
  // Per-Channel State Updates
  // ===========================================================================
  generate
    for (genvar i = 0; i < NUM_CHANNELS; i++) begin : gen_ch_state
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          ccr[i]       <= 32'h0;
          cndtr[i]     <= 32'h0;
          cpar[i]      <= 32'h0;
          cmar[i]      <= 32'h0;
          ctcnt[i]     <= 32'h0;
          cur_paddr[i] <= 32'h0;
          cur_maddr[i] <= 32'h0;
          tcif[i]      <= 1'b0;
          htif[i]      <= 1'b0;
          teif[i]      <= 1'b0;
        end else begin
          // Channel enable edge detection - reload transfer
          if (ccr[i][0] && !ch_en[i]) begin
            ctcnt[i]     <= cndtr[i];
            cur_paddr[i] <= cpar[i];
            cur_maddr[i] <= cmar[i];
          end

          // Transfer completion update
          if (state_q == DMA_DONE && active_ch == i[1:0]) begin
            ctcnt[i] <= ctcnt[i] - 1;

            // Address increment
            if (ch_pinc[i]) begin
              cur_paddr[i] <= cur_paddr[i] + get_addr_inc(ch_psize[i]);
            end
            if (ch_minc[i]) begin
              cur_maddr[i] <= cur_maddr[i] + get_addr_inc(ch_msize[i]);
            end

            // Half transfer interrupt
            if (ctcnt[i] == (cndtr[i] >> 1)) begin
              htif[i] <= 1'b1;
            end

            // Transfer complete
            if (ctcnt[i] == 1) begin
              tcif[i] <= 1'b1;
              if (ch_circ[i]) begin
                // Circular mode: reload
                ctcnt[i]     <= cndtr[i];
                cur_paddr[i] <= cpar[i];
                cur_maddr[i] <= cmar[i];
              end else begin
                // Normal mode: disable channel
                ccr[i][0] <= 1'b0;
              end
            end
          end

          // Register writes
          if (stb_i && we_i) begin
            if (adr_i[5:3] == i[2:0]) begin
              case (adr_i[2:0])
                3'h0: begin  // CCR
                  if (byte_sel_i[0]) ccr[i][7:0] <= dat_i[7:0];
                  if (byte_sel_i[1]) ccr[i][15:8] <= dat_i[15:8];
                  if (byte_sel_i[2]) ccr[i][23:16] <= dat_i[23:16];
                  if (byte_sel_i[3]) ccr[i][31:24] <= dat_i[31:24];
                end
                3'h1: begin  // CNDTR
                  if (!ch_en[i]) begin  // Only write when disabled
                    if (byte_sel_i[0]) cndtr[i][7:0] <= dat_i[7:0];
                    if (byte_sel_i[1]) cndtr[i][15:8] <= dat_i[15:8];
                    if (byte_sel_i[2]) cndtr[i][23:16] <= dat_i[23:16];
                    if (byte_sel_i[3]) cndtr[i][31:24] <= dat_i[31:24];
                  end
                end
                3'h2: begin  // CPAR
                  if (!ch_en[i]) begin
                    if (byte_sel_i[0]) cpar[i][7:0] <= dat_i[7:0];
                    if (byte_sel_i[1]) cpar[i][15:8] <= dat_i[15:8];
                    if (byte_sel_i[2]) cpar[i][23:16] <= dat_i[23:16];
                    if (byte_sel_i[3]) cpar[i][31:24] <= dat_i[31:24];
                  end
                end
                3'h3: begin  // CMAR
                  if (!ch_en[i]) begin
                    if (byte_sel_i[0]) cmar[i][7:0] <= dat_i[7:0];
                    if (byte_sel_i[1]) cmar[i][15:8] <= dat_i[15:8];
                    if (byte_sel_i[2]) cmar[i][23:16] <= dat_i[23:16];
                    if (byte_sel_i[3]) cmar[i][31:24] <= dat_i[31:24];
                  end
                end
                default: ;
              endcase
            end

            // IFCR - Interrupt Flag Clear (0x84 / word addr 0x21)
            if (adr_i == 6'h21) begin
              if (dat_i[i*4+1]) tcif[i] <= 1'b0;
              if (dat_i[i*4+2]) htif[i] <= 1'b0;
              if (dat_i[i*4+3]) teif[i] <= 1'b0;
            end
          end
        end
      end

      // Global interrupt flag
      assign gif[i]   = tcif[i] | htif[i] | teif[i];

      // Channel interrupt output
      assign irq_o[i] = (ch_tcie[i] & tcif[i]) | (ch_htie[i] & htif[i]) | (ch_teie[i] & teif[i]);
    end
  endgenerate

  // ===========================================================================
  // Read Data Mux
  // ===========================================================================
  always_comb begin
    dat_o = 32'h0;
    if (stb_i && !we_i) begin
      if (adr_i < 6'h20) begin
        // Per-channel registers
        case (adr_i[2:0])
          3'h0:    dat_o = ccr[adr_i[5:3]];
          3'h1:    dat_o = cndtr[adr_i[5:3]];
          3'h2:    dat_o = cpar[adr_i[5:3]];
          3'h3:    dat_o = cmar[adr_i[5:3]];
          3'h4:    dat_o = ctcnt[adr_i[5:3]];
          default: dat_o = 32'h0;
        endcase
      end else begin
        // Global registers
        case (adr_i)
          6'h20:   dat_o = isr_q;  // ISR
          6'h21:   dat_o = 32'h0;  // IFCR (write-only)
          6'h22:   dat_o = gcr_q;  // GCR
          default: dat_o = 32'h0;
        endcase
      end
    end
  end

endmodule
