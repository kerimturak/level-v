/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/

`timescale 1ns / 1ps
`include "ceres_defines.svh"
import ceres_param::*;

module memory_arbiter (
    input logic clk_i,
    input logic rst_ni,
    input ilowX_req_t icache_req_i,
    input dlowX_req_t dcache_req_i,
    output ilowX_res_t icache_res_o,
    output dlowX_res_t dcache_res_o,
    input lowX_res_t l2_res_i,       // Response from L2 cache
    output lowX_req_t l2_req_o       // Request to L2 cache
);

  localparam BOFFSET = $clog2(BLK_SIZE / 8);

  // Round-robin state for selecting which latched request to send
  typedef enum logic [1:0] {
    IDLE,
    ICACHE,
    DCACHE
  } round_e;
  round_e     round;

  // Latching registers for incoming requests
  ilowX_req_t icache_req_reg;
  dlowX_req_t dcache_req_reg;

  // Combinational logic for outputs using the latched request data
  always_comb begin
    // Response paths: l2_res_i.valid, artık L2 cache cevabının geçerli olduğunu bildiriyor.
    icache_res_o.valid = (round == ICACHE) && l2_res_i.valid;
    icache_res_o.ready = 1'b1;
    icache_res_o.blk   = l2_res_i.blk;

    dcache_res_o.valid = (round == DCACHE) && l2_res_i.valid;
    dcache_res_o.ready = 1'b1;
    dcache_res_o.data  = l2_res_i.blk;
    // L2 cache request: seçimi latched veriden yapıyoruz.
    if (round == DCACHE) begin
      l2_req_o.addr     = dcache_req_reg.addr;
      l2_req_o.valid    = dcache_req_reg.valid;
      l2_req_o.ready    = dcache_req_reg.ready;
      l2_req_o.rw       = dcache_req_reg.rw;
      l2_req_o.rw_size  = dcache_req_reg.rw_size;
      l2_req_o.data     = dcache_req_reg.data;
      l2_req_o.uncached = dcache_req_reg.uncached;
      l2_req_o.id       = 4'b0000;  // dcache ID: MSB=0
    end else begin  // ICACHE veya IDLE durumunda icache isteklerine öncelik veriyoruz.
      l2_req_o.addr     = icache_req_reg.addr;
      l2_req_o.valid    = icache_req_reg.valid;
      l2_req_o.ready    = icache_req_reg.ready;
      l2_req_o.rw       = 1'b0;  // ICache always reads
      l2_req_o.rw_size  = NO_SIZE;  // ICache reads full cache line
      l2_req_o.data     = '0;
      l2_req_o.uncached = icache_req_reg.uncached;
      l2_req_o.id       = 4'b1000;  // icache ID: MSB=1
    end
  end

  // Sequential block: Latching istekler ve round state güncellemesi
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      round          <= IDLE;
      icache_req_reg <= '{default: 0};
      dcache_req_reg <= '{rw_size: NO_SIZE, default: 0};
    end else begin
      // Yeni istekleri latch’la (varsa). Tek cycle’lık pulse’u register’da tutuyoruz.
      if (!icache_req_reg.valid && icache_req_i.valid) icache_req_reg <= icache_req_i;
      if (!dcache_req_reg.valid && dcache_req_i.valid) dcache_req_reg <= dcache_req_i;

      // L2 cache cevabı geçerli ise (l2_res_i.valid aktifse) latched istek temizlenir ve round state güncellenir.
      if (l2_res_i.valid || round == IDLE) begin
        case (round)
          ICACHE: begin
            icache_req_reg.valid <= 1'b0;  // İstek işlendi, temizle
            // Eğer dcache'te bekleyen istek varsa onu seç, yoksa ICACHE'da kal.
            round <= dcache_req_reg.valid ? DCACHE : icache_req_reg.valid && !l2_res_i.valid ? ICACHE : IDLE;
          end
          DCACHE: begin
            dcache_req_reg.valid <= 1'b0;  // İstek işlendi, temizle
            // Eğer icache'te bekleyen istek varsa onu seç, yoksa DCACHE'te kal.
            round <= icache_req_reg.valid ? ICACHE : dcache_req_reg.valid && !l2_res_i.valid ? DCACHE : IDLE;
          end
          IDLE: begin
            if (icache_req_reg.valid) round <= ICACHE;
            else if (dcache_req_reg.valid) round <= DCACHE;
            else round <= IDLE;
          end
          default: round <= IDLE;
        endcase
      end
      // Eğer l2_res_i.valid düşükse, round sabit kalır ve latch'lenen istek sürekli gönderilir.
    end
  end

endmodule
