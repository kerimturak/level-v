`timescale 1ns / 1ps

module tb_dcache_writeback;
  import ceres_param::*;

  // Parameters - Very small 2-way 512B config to force evictions
  localparam int DC_WAY_TB = 2;
  localparam int DC_CAPACITY_TB = 512 * 8;  // 512 bytes total
  localparam int BLK_SIZE_TB = 128;  // 16 byte cache lines
  localparam int XLEN_TB = 32;
  localparam int NUM_SETS = DC_CAPACITY_TB / (DC_WAY_TB * BLK_SIZE_TB);  // 16 sets

  // Clock and reset
  logic                           clk = 0;
  logic                           rst_n;

  // DCache interfaces
  ceres_param::dcache_req_t       cache_req;
  ceres_param::dcache_res_t       cache_res;
  ceres_param::dlowX_req_t        lowX_req;
  ceres_param::dlowX_res_t        lowX_res;
  logic                           flush;
  logic                           fencei_stall;

  // Simple memory model with write-first behavior
  logic                     [7:0] memory          [logic [31:0]];

  // Test statistics
  int                             store_count = 0;
  int                             load_count = 0;
  int                             wb_count = 0;
  int                             error_count = 0;

  // DCache instance - using simple dcache
  dcache_simple dut (
      .clk_i         (clk),
      .rst_ni        (rst_n),
      .flush_i       (flush),
      .cache_req_i   (cache_req),
      .cache_res_o   (cache_res),
      .lowX_res_i    (lowX_res),
      .lowX_req_o    (lowX_req),
      .fencei_stall_o(fencei_stall)
  );

  // Clock generation
  always #5 clk = ~clk;

  // Memory model - 1 cycle latency (more realistic)
  logic         pending_req;
  logic         pending_rw;
  logic [ 31:0] pending_addr;
  logic [127:0] pending_data;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      lowX_res.valid <= 1'b0;
      lowX_res.ready <= 1'b1;
      lowX_res.data <= '0;
      pending_req <= 1'b0;
    end else begin
      lowX_res.ready <= 1'b1;

      // Accept new request
      if (lowX_req.valid && lowX_res.ready && !pending_req) begin
        pending_req <= 1'b1;
        pending_rw <= lowX_req.rw;
        pending_addr <= lowX_req.addr;
        pending_data <= lowX_req.data;
        lowX_res.valid <= 1'b0;
      end  // Process pending request (1 cycle later)
      else if (pending_req) begin
        pending_req <= 1'b0;
        lowX_res.valid <= 1'b1;

        if (pending_rw) begin
          // Write to memory - use blocking assignment for associative array
          for (int i = 0; i < 16; i++) begin
            memory[pending_addr+i] = pending_data[i*8+:8];
          end
          lowX_res.data  <= '0;
          lowX_res.valid <= 1'b1;
          $display("[MEM] Write @ 0x%08x: data=0x%08x_%08x_%08x_%08x", pending_addr, pending_data[127:96], pending_data[95:64], pending_data[63:32], pending_data[31:0]);
          wb_count++;
        end else begin
          // Read from memory - return zero for uninitialized locations
          for (int i = 0; i < 16; i++) begin
            if (memory.exists(pending_addr + i)) lowX_res.data[i*8+:8] <= memory[pending_addr+i];
            else lowX_res.data[i*8+:8] <= 8'h00;
          end
          lowX_res.valid <= 1'b1;
          $display("[MEM] Read @ 0x%08x: data=0x%02x_%02x_%02x_%02x", pending_addr, memory.exists(pending_addr + 3) ? memory[pending_addr+3] : 8'h00, memory.exists(pending_addr + 2
                   ) ? memory[pending_addr+2] : 8'h00, memory.exists(pending_addr + 1) ? memory[pending_addr+1] : 8'h00, memory.exists(pending_addr + 0) ? memory[pending_addr+0] : 8'h00);
        end
      end else begin
        lowX_res.valid <= 1'b0;
      end
    end
  end

  // Task to perform a store
  task automatic do_store(input logic [31:0] addr, input logic [31:0] data);
    int timeout_cnt = 0;
    begin
      // Wait for cache to be ready
      while (!cache_res.ready) begin
        @(posedge clk);
        timeout_cnt++;
        if (timeout_cnt > 100) begin
          $display("ERROR: Cache not ready before store");
          error_count++;
          return;
        end
      end

      @(posedge clk);
      cache_req.valid = 1'b1;
      cache_req.ready = 1'b1;
      cache_req.addr = addr;
      cache_req.rw = 1'b1;
      cache_req.rw_size = WORD;  // Word
      cache_req.data = data;
      cache_req.uncached = 1'b0;

      // Wait for cache to respond
      timeout_cnt = 0;
      while (!cache_res.valid) begin
        @(posedge clk);
        timeout_cnt++;
        if (timeout_cnt > 100) begin
          $display("ERROR: Store timeout @ 0x%08x", addr);
          error_count++;
          cache_req.valid = 1'b0;
          return;
        end
      end

      $display("[STORE] @ 0x%08x = 0x%08x", addr, data);
      @(posedge clk);
      cache_req.valid = 1'b0;
      store_count++;
    end
  endtask

  // Task to perform a load
  task automatic do_load(input logic [31:0] addr, output logic [31:0] data);
    int timeout_cnt = 0;
    begin
      // Wait for cache to be ready
      while (!cache_res.ready) begin
        @(posedge clk);
        timeout_cnt++;
        if (timeout_cnt > 100) begin
          $display("ERROR: Cache not ready before load");
          error_count++;
          data = 32'hDEADBEEF;
          return;
        end
      end

      @(posedge clk);
      cache_req.valid = 1'b1;
      cache_req.ready = 1'b1;
      cache_req.addr = addr;
      cache_req.rw = 1'b0;
      cache_req.rw_size = WORD;  // Word
      cache_req.uncached = 1'b0;

      // Wait for cache to respond
      timeout_cnt = 0;
      while (!cache_res.valid) begin
        @(posedge clk);
        timeout_cnt++;
        if (timeout_cnt > 100) begin
          $display("ERROR: Load timeout @ 0x%08x", addr);
          error_count++;
          cache_req.valid = 1'b0;
          data = 32'hDEADBEEF;
          return;
        end
      end

      data = cache_res.data;
      $display("[LOAD]  @ 0x%08x = 0x%08x (miss=%b lowX_valid=%b lowX_data[31:0]=0x%08x)", addr, data, cache_res.miss, lowX_res.valid, lowX_res.data[31:0]);

      @(posedge clk);
      cache_req.valid = 1'b0;
      load_count++;
    end
  endtask

  // Test sequence
  initial begin
    logic [31:0] read_data;

    // Initialize
    rst_n = 0;
    flush = 0;
    cache_req = '0;

    repeat (10) @(posedge clk);
    rst_n = 1;
    repeat (5) @(posedge clk);

    $display("========================================");
    $display("DCache Writeback Test");
    $display("Config: 2-way, 512B, 16 sets");
    $display("Cache line size: 16 bytes");
    $display("========================================\n");

    // Test 1: Fill both ways of set 0 (addresses 0x8000_0000, 0x8000_0100)
    $display("\n=== Test 1: Store same address twice to set dirty bit ===");
    do_store(32'h80000000, 32'hAAAA0000);  // First store - miss, fills cache, dirty=0
    do_store(32'h80000000, 32'hAAAA1111);  // Second store - hit, should set dirty=1

    $display("\n=== Test 1b: Fill set 0, both ways ===");
    do_store(32'h80000100, 32'hBBBB0100);  // Set 0, Way 1
    do_store(32'h80000100, 32'hBBBB0200);  // Set dirty on way 1

    // Test 2: Read back - should hit
    $display("\n=== Test 2: Read from set 0 (hits) ===");
    do_load(32'h80000000, read_data);
    if (read_data !== 32'hAAAA0000) begin
      $display("ERROR: Expected 0xAAAA0000, got 0x%08x", read_data);
      error_count++;
    end

    do_load(32'h80000100, read_data);
    if (read_data !== 32'hBBBB0100) begin
      $display("ERROR: Expected 0xBBBB0100, got 0x%08x", read_data);
      error_count++;
    end

    // Test 3: Write to set 0 again, forcing eviction (should evict way 0)
    $display("\n=== Test 3: Force eviction with 3rd write to set 0 ===");
    do_store(32'h80000200, 32'hCCCC0200);  // Set 0, causes eviction

    // Test 4: Read evicted data from memory (should cause miss + writeback)
    $display("\n=== Test 4: Read evicted address (miss + possible WB) ===");
    do_load(32'h80000000, read_data);
    if (read_data !== 32'hAAAA0000) begin
      $display("ERROR: Evicted data lost! Expected 0xAAAA0000, got 0x%08x", read_data);
      error_count++;
    end

    // Test 5: Fill multiple sets to test different indices
    $display("\n=== Test 5: Fill multiple sets ===");
    for (int i = 0; i < 8; i++) begin
      do_store(32'h80000000 + (i << 4), 32'hDEAD0000 + i);  // Different sets
    end

    // Test 6: Read them back
    $display("\n=== Test 6: Read back from multiple sets ===");
    for (int i = 0; i < 8; i++) begin
      do_load(32'h80000000 + (i << 4), read_data);
      if (read_data !== (32'hDEAD0000 + i)) begin
        $display("ERROR: Set %0d - Expected 0x%08x, got 0x%08x", i, 32'hDEAD0000 + i, read_data);
        error_count++;
      end
    end

    // Final report
    $display("\n========================================");
    $display("Test Results");
    $display("========================================");
    $display("Stores:     %0d", store_count);
    $display("Loads:      %0d", load_count);
    $display("Writebacks: %0d", wb_count);
    $display("Errors:     %0d", error_count);
    $display("========================================");

    if (error_count == 0) begin
      $display("✅ TEST PASSED - All operations correct!");
    end else begin
      $display("❌ TEST FAILED - %0d errors found", error_count);
    end

    #100;
    $finish;
  end

  // Watchdog timeout
  initial begin
    #100_000;  // 100us timeout
    $display("\n!!! TIMEOUT !!!");
    $finish;
  end

endmodule
