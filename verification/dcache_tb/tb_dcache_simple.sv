// =============================================================================
// Simple DCache Test - Single Address
// =============================================================================

`timescale 1ns / 1ps

module tb_dcache_simple;

  import ceres_param::*;

  logic clk, rst_n;

  // Clock
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Reset
  initial begin
    rst_n = 0;
    repeat (5) @(posedge clk);
    rst_n = 1;
  end

  // Interfaces
  dcache_req_t         cache_req;
  dcache_res_t         cache_res;
  dlowX_req_t          lowx_req;
  dlowX_res_t          lowx_res;
  logic                flush;

  // Simple memory
  logic        [  7:0] memory    [65536];
  logic        [127:0] mem_rdata;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      lowx_res.valid <= 0;
      lowx_res.data  <= '0;
      for (int i = 0; i < 65536; i++) memory[i] <= i[7:0];
    end else begin
      lowx_res.valid <= 0;
      if (lowx_req.valid) begin
        lowx_res.valid <= 1;
        if (lowx_req.rw) begin
          for (int i = 0; i < 16; i++) memory[lowx_req.addr[15:0]+i] <= lowx_req.data[i*8+:8];
          $display("[%0t] MEM Write: addr=0x%h", $time, lowx_req.addr);
        end else begin
          for (int i = 0; i < 16; i++) mem_rdata[i*8+:8] = memory[lowx_req.addr[15:0]+i];
          lowx_res.data <= mem_rdata;
          $display("[%0t] MEM Read: addr=0x%h data=0x%h", $time, lowx_req.addr, mem_rdata);
        end
      end
    end
  end

  assign lowx_req.ready = 1;
  assign lowx_res.ready = 1;

  // DUT
  dcache #(
      .cache_req_t(dcache_req_t),
      .cache_res_t(dcache_res_t),
      .lowX_req_t (dlowX_req_t),
      .lowX_res_t (dlowX_res_t),
      .CACHE_SIZE (512),
      .BLK_SIZE   (128),
      .XLEN       (32),
      .NUM_WAY    (2)
  ) dut (
      .clk_i         (clk),
      .rst_ni        (rst_n),
      .flush_i       (flush),
      .cache_req_i   (cache_req),
      .cache_res_o   (cache_res),
      .lowX_res_i    (lowx_res),
      .lowX_req_o    (lowx_req),
      .fencei_stall_o()
  );

  // Test
  initial begin
    cache_req = '0;
    cache_req.ready = 1;
    flush = 0;

    @(posedge rst_n);
    repeat (10) @(posedge clk);

    $display("\n=== SIMPLE TEST: Single Address ===\n");

    // Test 1: Read addr=0x1000 (should MISS, fill from memory)
    $display("[%0t] TEST: Read addr=0x1000 (expect MISS)", $time);
    @(posedge clk);
    cache_req.valid <= 1;
    cache_req.addr <= 32'h1000;
    cache_req.rw <= 0;
    cache_req.rw_size <= WORD;  // Word  // word

    // Wait for response
    wait (cache_res.valid);
    $display("[%0t] RESULT: data=0x%h miss=%b", $time, cache_res.data, cache_res.miss);
    @(posedge clk);
    cache_req.valid <= 0;

    // Check internal state
    $display("[%0t] DUT State: valid_vec=%b hit_vec=%b", $time, dut.cache_valid_vec, dut.cache_hit_vec);

    repeat (5) @(posedge clk);

    // Test 2: Read same address again (should HIT)
    $display("[%0t] TEST: Read addr=0x1000 again (expect HIT)", $time);
    @(posedge clk);
    cache_req.valid <= 1;
    cache_req.addr <= 32'h1000;
    cache_req.rw <= 0;
    cache_req.rw_size <= WORD;  // Word

    wait (cache_res.valid);
    $display("[%0t] RESULT: data=0x%h miss=%b", $time, cache_res.data, cache_res.miss);
    @(posedge clk);
    cache_req.valid <= 0;

    $display("[%0t] DUT State: valid_vec=%b hit_vec=%b", $time, dut.cache_valid_vec, dut.cache_hit_vec);

    repeat (10) @(posedge clk);
    $finish;
  end

  // Waveform
  initial begin
    $dumpfile("simple.vcd");
    $dumpvars(0, tb_dcache_simple);
  end

endmodule
