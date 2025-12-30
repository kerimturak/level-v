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
    input lowX_res_t mem_bus_res_i,
    output lowX_req_t mem_bus_req_o
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
    // Response paths: mem_bus_res_i.valid, artık bellek cevabının geçerli olduğunu bildiriyor.
    icache_res_o.valid = (round == ICACHE) && mem_bus_res_i.valid;
    icache_res_o.ready = 1'b1;
    icache_res_o.blk   = mem_bus_res_i.blk;

    dcache_res_o.valid = (round == DCACHE) && mem_bus_res_i.valid;
    dcache_res_o.ready = 1'b1;
    dcache_res_o.data  = mem_bus_res_i.blk;
    // Memory request: seçimi latched veriden yapıyoruz.
    if (round == DCACHE) begin
      mem_bus_req_o.addr     = dcache_req_reg.addr;
      mem_bus_req_o.valid    = dcache_req_reg.valid;
      mem_bus_req_o.ready    = dcache_req_reg.ready;
      mem_bus_req_o.rw       = dcache_req_reg.rw;
      mem_bus_req_o.rw_size  = dcache_req_reg.rw_size;
      mem_bus_req_o.data     = dcache_req_reg.data;
      mem_bus_req_o.uncached = dcache_req_reg.uncached;
    end else begin  // ICACHE veya IDLE durumunda icache isteklerine öncelik veriyoruz.
      mem_bus_req_o.addr     = icache_req_reg.addr;
      mem_bus_req_o.valid    = icache_req_reg.valid;
      mem_bus_req_o.ready    = icache_req_reg.ready;
      mem_bus_req_o.rw       = 1'b0;  // ICache always reads
      mem_bus_req_o.rw_size  = NO_SIZE;  // ICache reads full cache line
      mem_bus_req_o.data     = '0;
      mem_bus_req_o.uncached = icache_req_reg.uncached;
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

      // Bellek cevabı geçerli ise (mem_bus_res_i.valid aktifse) latched istek temizlenir ve round state güncellenir.
      if (mem_bus_res_i.valid || round == IDLE) begin
        case (round)
          ICACHE: begin
            icache_req_reg.valid <= 1'b0;  // İstek işlendi, temizle
            // Eğer dcache'te bekleyen istek varsa onu seç, yoksa ICACHE'da kal.
            round <= dcache_req_reg.valid ? DCACHE : icache_req_reg.valid && !mem_bus_res_i.valid ? ICACHE : IDLE;
          end
          DCACHE: begin
            dcache_req_reg.valid <= 1'b0;  // İstek işlendi, temizle
            // Eğer icache'te bekleyen istek varsa onu seç, yoksa DCACHE'te kal.
            round <= icache_req_reg.valid ? ICACHE : dcache_req_reg.valid && !mem_bus_res_i.valid ? DCACHE : IDLE;
          end
          IDLE: begin
            if (icache_req_reg.valid) round <= ICACHE;
            else if (dcache_req_reg.valid) round <= DCACHE;
            else round <= IDLE;
          end
          default: round <= IDLE;
        endcase
      end
      // Eğer mem_bus_res_i.valid düşükse, round sabit kalır ve latch'lenen istek sürekli gönderilir.
    end
  end

endmodule
