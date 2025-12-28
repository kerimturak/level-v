// =============================================================================
// Single Set DCache Test - All requests target same set
// =============================================================================
// Purpose: Test n-way associativity by forcing all requests to same set
// Features:
// - All addresses map to the same cache set
// - Random request sizes (byte/half/word)
// - Random read/write operations
// - Repeated reads/writes to same addresses
// - Observe eviction and replacement policy behavior
// =============================================================================

`timescale 1ns / 1ps

module tb_dcache_single_set;

  import ceres_param::*;

  logic clk, rst_n;
  int cycle_count;
  int test_count;
  int error_count;

  // Clock & reset
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  initial begin
    rst_n = 0;
    cycle_count = 0;
    repeat (5) @(posedge clk);
    rst_n = 1;
  end

  always @(posedge clk) begin
    if (rst_n) cycle_count++;
  end

  // Interfaces
  dcache_req_t         cache_req;
  dcache_res_t         cache_res;
  dlowX_req_t          lowx_req;
  dlowX_res_t          lowx_res;
  logic                flush;
  logic                fencei_stall;

  // Memory model (64KB)
  logic        [  7:0] memory       [65536];
  logic        [127:0] mem_rdata;

  // DCache parameters (from ceres_param)
  localparam CACHE_SIZE_PARAM = DC_SIZE;  // Cache size in bits
  localparam NUM_WAY_PARAM = DC_WAY;  // Number of ways
  localparam XLEN_PARAM = 32;

  localparam NUM_SET = (CACHE_SIZE_PARAM / (BLK_SIZE / 8 * NUM_WAY_PARAM));
  localparam OFFSET_BITS = $clog2(BLK_SIZE / 8);  // 4 bits for 16-byte blocks
  localparam INDEX_BITS = $clog2(NUM_SET);  // bits for set index
  localparam TAG_BITS = XLEN_PARAM - INDEX_BITS - OFFSET_BITS;

  // DUT
  dcache #(
      .cache_req_t(dcache_req_t),
      .cache_res_t(dcache_res_t),
      .lowX_res_t (dlowX_res_t),
      .lowX_req_t (dlowX_req_t),
      .CACHE_SIZE (DC_SIZE),
      .BLK_SIZE   (BLK_SIZE),
      .NUM_WAY    (DC_WAY)
  ) dut (
      .clk_i         (clk),
      .rst_ni        (rst_n),
      .flush_i       (flush),
      .cache_req_i   (cache_req),
      .cache_res_o   (cache_res),
      .lowX_req_o    (lowx_req),
      .lowX_res_i    (lowx_res),
      .fencei_stall_o(fencei_stall)
  );

  // Initialize memory with pattern
  initial begin
    for (int i = 0; i < 65536; i++) begin
      memory[i] = i[7:0] ^ i[15:8];
    end
  end

  // Memory controller - responds to lowX requests
  always @(posedge clk) begin
    if (!rst_n) begin
      lowx_res.valid <= 0;
      lowx_res.data  <= 0;
    end else begin
      if (lowx_req.valid && lowx_req.ready) begin
        if (lowx_req.rw) begin
          // Write request (writeback)
          for (int i = 0; i < 16; i++) begin
            memory[lowx_req.addr[15:0]+i] <= lowx_req.data[i*8+:8];
          end
          lowx_res.valid <= 1;
          lowx_res.data  <= 0;
        end else begin
          // Read request
          for (int i = 0; i < 16; i++) begin
            mem_rdata[i*8+:8] = memory[lowx_req.addr[15:0]+i];
          end
          lowx_res.data  <= mem_rdata;
          lowx_res.valid <= 1;
        end
      end else begin
        lowx_res.valid <= 0;
      end
    end
  end

  assign lowx_req.ready = 1'b1;  // Always ready

  // ============================================================================
  // Address generation - ALL addresses target SAME SET
  // ============================================================================
  // Strategy: Fix the index bits, vary tag and offset
  // Address format: [TAG | INDEX | OFFSET]
  //                 [31:INDEX_BITS+OFFSET_BITS | INDEX_BITS+OFFSET_BITS-1:OFFSET_BITS | OFFSET_BITS-1:0]

  localparam TARGET_SET = 3;  // Choose set 3 (arbitrary, can be any valid set)

  // Generate random addresses that all map to TARGET_SET
  function automatic logic [31:0] gen_same_set_addr(input int tag_val, input int offset_val);
    logic [31:0] addr;
    addr = 0;
    addr[OFFSET_BITS-1:0] = offset_val[OFFSET_BITS-1:0];
    addr[INDEX_BITS+OFFSET_BITS-1:OFFSET_BITS] = TARGET_SET[INDEX_BITS-1:0];
    addr[31:INDEX_BITS+OFFSET_BITS] = tag_val[TAG_BITS-1:0];
    return addr;
  endfunction

  // ============================================================================
  // Test addresses - different tags, same set
  // ============================================================================
  localparam NUM_ADDRS = 8;  // More addresses than ways to force evictions
  logic [31:0] test_addrs[NUM_ADDRS];

  initial begin
    // Generate addresses with different tags but same set
    for (int i = 0; i < NUM_ADDRS; i++) begin
      test_addrs[i] = gen_same_set_addr(i, 0);  // Different tags, offset=0
      $display("Test Address[%0d] = 0x%08x (Tag=%0d, Set=%0d, Offset=0)", i, test_addrs[i], i, TARGET_SET);
    end
  end

  // ============================================================================
  // Test task: Issue random request
  // ============================================================================
  task automatic issue_request(input logic [31:0] addr, input logic is_write, input logic [1:0] size,  // 01=byte, 10=half, 11=word
                               input logic [31:0] wdata);
    cache_req.valid = 1;
    cache_req.addr = addr;
    cache_req.data = wdata;
    cache_req.rw = is_write;
    cache_req.rw_size = rw_size_e'(size);
    cache_req.uncached = 0;
    cache_req.ready = 1;

    @(posedge clk);

    // Wait for response
    while (!cache_res.valid) @(posedge clk);

    cache_req.valid = 0;
    cache_req.rw = 0;

    if (!is_write) begin
      $display("[%0t] READ  addr=0x%08x size=%0d data=0x%08x", $time, addr, size, cache_res.data);
    end else begin
      $display("[%0t] WRITE addr=0x%08x size=%0d data=0x%08x", $time, addr, size, wdata);
    end

    test_count++;
  endtask

  // ============================================================================
  // Main test
  // ============================================================================
  initial begin
    test_count = 0;
    error_count = 0;
    flush = 0;
    cache_req = '0;

    // Wait for reset
    wait (rst_n);
    repeat (5) @(posedge clk);

    $display("\n========================================");
    $display("Single Set DCache Test");
    $display("========================================");
    $display("Cache Config:");
    $display("  Size: %0d bytes", CACHE_SIZE);
    $display("  Block: %0d bytes", BLK_SIZE / 8);
    $display("  Ways: %0d", NUM_WAY);
    $display("  Sets: %0d", NUM_SET);
    $display("  Target Set: %0d", TARGET_SET);
    $display("========================================\n");

    // ========================================================================
    // Phase 1: Fill cache with different addresses (same set)
    // ========================================================================
    $display("\n=== Phase 1: Initial fills ===");
    for (int i = 0; i < NUM_ADDRS; i++) begin
      automatic logic [31:0] addr = test_addrs[i];
      automatic logic [ 1:0] size = 2'b11;  // Word access
      automatic logic [31:0] wdata = 32'hDEAD_0000 + i;

      // Write to each address
      issue_request(addr, 1'b1, size, wdata);
      repeat ($urandom_range(1, 3)) @(posedge clk);
    end

    // ========================================================================
    // Phase 2: Read back in different order
    // ========================================================================
    $display("\n=== Phase 2: Read back (different order) ===");
    for (int i = NUM_ADDRS - 1; i >= 0; i--) begin
      automatic logic [31:0] addr = test_addrs[i];
      automatic logic [ 1:0] size = 2'b11;

      issue_request(addr, 1'b0, size, 32'h0);
      repeat ($urandom_range(1, 2)) @(posedge clk);
    end

    // ========================================================================
    // Phase 3: Random reads/writes with random sizes
    // ========================================================================
    $display("\n=== Phase 3: Random operations ===");
    for (int test = 0; test < 50; test++) begin
      automatic int          addr_idx = $urandom_range(0, NUM_ADDRS - 1);
      automatic logic [31:0] base_addr = test_addrs[addr_idx];
      automatic int          offset = $urandom_range(0, 12);  // Random offset within block
      automatic logic [31:0] addr = base_addr + offset;
      automatic logic        is_write = $urandom_range(0, 1);
      automatic logic [ 1:0] size = $urandom_range(1, 3);  // 01, 10, or 11
      automatic logic [31:0] wdata = $urandom();

      issue_request(addr, is_write, size, wdata);
      repeat ($urandom_range(0, 2)) @(posedge clk);
    end

    // ========================================================================
    // Phase 4: Repeated reads/writes to SAME addresses
    // ========================================================================
    $display("\n=== Phase 4: Repeated access to same addresses ===");
    for (int i = 0; i < NUM_ADDRS; i++) begin
      automatic logic [31:0] addr = test_addrs[i];

      // Write multiple times
      for (int j = 0; j < 3; j++) begin
        automatic logic [ 1:0] size = 2'b11;
        automatic logic [31:0] wdata = 32'hCAFE_0000 + (i << 8) + j;
        issue_request(addr, 1'b1, size, wdata);
        @(posedge clk);
      end

      // Read multiple times
      for (int j = 0; j < 3; j++) begin
        automatic logic [1:0] size = 2'b11;
        issue_request(addr, 1'b0, size, 32'h0);
        @(posedge clk);
      end
    end

    // ========================================================================
    // Phase 5: Mixed sizes on same address
    // ========================================================================
    $display("\n=== Phase 5: Mixed size accesses ===");
    begin
      automatic logic [31:0] addr = test_addrs[0];

      // Word write
      issue_request(addr, 1'b1, 2'b11, 32'h12345678);
      @(posedge clk);

      // Byte reads from same word
      issue_request(addr + 0, 1'b0, 2'b01, 32'h0);
      issue_request(addr + 1, 1'b0, 2'b01, 32'h0);
      issue_request(addr + 2, 1'b0, 2'b01, 32'h0);
      issue_request(addr + 3, 1'b0, 2'b01, 32'h0);

      // Half reads
      issue_request(addr + 0, 1'b0, 2'b10, 32'h0);
      issue_request(addr + 2, 1'b0, 2'b10, 32'h0);

      // Word read
      issue_request(addr, 1'b0, 2'b11, 32'h0);
    end

    // ========================================================================
    // Phase 6: Stress test - Many operations on same set
    // ========================================================================
    $display("\n=== Phase 6: Stress test ===");
    for (int test = 0; test < 100; test++) begin
      automatic int          addr_idx = $urandom_range(0, NUM_ADDRS - 1);
      automatic logic [31:0] addr = test_addrs[addr_idx];
      automatic logic        is_write = $urandom_range(0, 1);
      automatic logic [ 1:0] size = $urandom_range(1, 3);
      automatic logic [31:0] wdata = $urandom();

      issue_request(addr, is_write, size, wdata);

      // Sometimes no delay, sometimes delay
      if ($urandom_range(0, 2) == 0) begin
        repeat ($urandom_range(1, 5)) @(posedge clk);
      end
    end

    // Done
    repeat (10) @(posedge clk);

    $display("\n========================================");
    $display("Test Complete!");
    $display("Total operations: %0d", test_count);
    $display("Errors: %0d", error_count);
    $display("========================================\n");

    $finish;
  end

  // Timeout
  initial begin
    #100000;
    $display("\nERROR: Timeout!");
    $finish;
  end

  // Waveform dump
  initial begin
    $dumpfile("single_set.vcd");
    $dumpvars(0, tb_dcache_single_set);
  end

endmodule
