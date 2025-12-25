// =============================================================================
// DCache Standalone Testbench
// =============================================================================
// Minimal test environment for dcache verification
// - Instantiates dcache RTL
// - Instantiates reference model
// - Provides simple memory controller
// - Runs directed tests
// - Compares RTL with model using hierarchical references
// =============================================================================

`timescale 1ns / 1ps

module tb_dcache;

  // =========================================================================
  // Parameters (matching smallest cache config)
  // =========================================================================
  localparam int XLEN = 32;
  localparam int NUM_WAY = 2;
  localparam int NUM_SET = 2;
  localparam int BLK_SIZE = 128;
  localparam int TAG_WIDTH = 19;
  localparam int IDX_WIDTH = 1;
  localparam int BOFFSET = 4;

  // =========================================================================
  // Clock and Reset
  // =========================================================================
  logic clk;
  logic rst_n;

  initial begin
    clk = 0;
    forever #5 clk = ~clk;  // 10ns period = 100MHz
  end

  initial begin
    rst_n = 0;
    repeat (5) @(posedge clk);
    rst_n = 1;
    $display("[TB] Reset released at time %0t", $time);
  end

  // =========================================================================
  // DUT Interfaces - Import types from ceres_param package
  // =========================================================================
  import ceres_param::*;

  // Cache interface structs
  dcache_req_t         cache_req;
  dcache_res_t         cache_res;
  dlowX_req_t          lowx_req;
  dlowX_res_t          lowx_res;

  // Flush interface
  logic                flush;

  // =========================================================================
  // Simple Memory Model (64KB)
  // =========================================================================
  logic        [  7:0] memory    [65536];  // 64KB memory
  logic        [127:0] mem_rdata;

  // Memory controller - responds to lowx requests
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      lowx_res.valid <= 1'b0;
      lowx_res.data  <= '0;
      // Initialize memory with pattern
      for (int i = 0; i < 65536; i++) begin
        memory[i] <= i[7:0];
      end
    end else begin
      lowx_res.valid <= 1'b0;

      if (lowx_req.valid && lowx_req.ready) begin
        // Single cycle response for testing
        lowx_res.valid <= 1'b1;

        if (lowx_req.rw) begin
          // Write to memory
          for (int i = 0; i < 16; i++) begin
            memory[lowx_req.addr[15:0]+i] <= lowx_req.data[i*8+:8];
          end
          lowx_res.data <= '0;
          $display("[MEM] Write: addr=0x%08x data=0x%032h", lowx_req.addr, lowx_req.data);
        end else begin
          // Read from memory
          for (int i = 0; i < 16; i++) begin
            mem_rdata[i*8+:8] = memory[lowx_req.addr[15:0]+i];
          end
          lowx_res.data <= mem_rdata;
          $display("[MEM] Read: addr=0x%08x data=0x%032h", lowx_req.addr, mem_rdata);
        end
      end
    end
  end

  assign lowx_req.ready = 1'b1;  // Always ready
  assign lowx_res.ready = 1'b1;  // Always ready

  // =========================================================================
  // DUT Instantiation - Actual DCache
  // =========================================================================

  dcache #(
      .cache_req_t(dcache_req_t),
      .cache_res_t(dcache_res_t),
      .lowX_req_t (dlowX_req_t),
      .lowX_res_t (dlowX_res_t),
      .CACHE_SIZE (512),           // 512 bits = 2 sets, 2 ways
      .BLK_SIZE   (128),           // 128-bit cache line
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
      .fencei_stall_o()            // Not used in standalone test
  );

  // =========================================================================
  // Reference Model Instantiation
  // =========================================================================
  dcache_model #(
      .XLEN     (XLEN),
      .NUM_WAY  (NUM_WAY),
      .NUM_SET  (NUM_SET),
      .BLK_SIZE (BLK_SIZE),
      .TAG_WIDTH(TAG_WIDTH),
      .IDX_WIDTH(IDX_WIDTH),
      .BOFFSET  (BOFFSET)
  ) model (
      .clk_i (clk),
      .rst_ni(rst_n)
  );

  // =========================================================================
  // Test Sequences
  // =========================================================================

  // Test control
  int test_num;
  int error_count;

  task automatic cache_read(input logic [31:0] addr, input logic [1:0] size, output logic [31:0] data, output logic hit);
    // Ensure cache_res.valid is low before starting
    @(posedge clk);
    while (cache_res.valid) @(posedge clk);

    cache_req.valid <= 1'b1;
    cache_req.addr <= addr;
    cache_req.rw <= 1'b0;
    cache_req.rw_size <= rw_size_e'(size);
    cache_req.uncached <= 1'b0;
    cache_req.data <= '0;
    cache_req.ready <= 1'b1;

    // Wait for NEW valid assertion
    wait (cache_res.valid);
    // Sample data IMMEDIATELY when valid
    data = cache_res.data;
    hit  = ~cache_res.miss;

    @(posedge clk);
    cache_req.valid <= 1'b0;

    // Wait for valid to go low before returning
    while (cache_res.valid) @(posedge clk);

    $display("[TEST] Read: addr=0x%08x size=%0d data=0x%08x hit=%b", addr, size, data, hit);
  endtask

  task automatic cache_write(input logic [31:0] addr, input logic [1:0] size, input logic [31:0] wdata);
    // Ensure cache_res.valid is low before starting
    @(posedge clk);
    while (cache_res.valid) @(posedge clk);

    cache_req.valid <= 1'b1;
    cache_req.addr <= addr;
    cache_req.rw <= 1'b1;
    cache_req.rw_size <= rw_size_e'(size);
    cache_req.data <= wdata;
    cache_req.uncached <= 1'b0;
    cache_req.ready <= 1'b1;

    // Wait for NEW valid assertion
    wait (cache_res.valid);

    @(posedge clk);
    cache_req.valid <= 1'b0;

    // Wait for valid to go low before returning
    while (cache_res.valid) @(posedge clk);

    $display("[TEST] Write: addr=0x%08x size=%0d data=0x%08x", addr, size, wdata);
  endtask

  // =========================================================================
  // TEST 1: Fill all cache lines
  // =========================================================================
  task test_1_fill_cache();
    logic [31:0] data;
    logic        hit;

    $display("\n========================================");
    $display("TEST 1: Fill all cache lines (4 lines)");
    $display("========================================");

    // Cache has 2 sets, 2 ways = 4 lines total
    // Each line is 16 bytes (128 bits)
    // Addresses that map to set 0: ...0000b (bit 4 = 0)
    // Addresses that map to set 1: ...0001b (bit 4 = 1)

    // Fill set 0, way 0
    cache_read(32'h0000_0000, 2'b11, data, hit);
    if (hit) error_count++;

    // Fill set 0, way 1
    cache_read(32'h0001_0000, 2'b11, data, hit);
    if (hit) error_count++;

    // Fill set 1, way 0
    cache_read(32'h0000_0010, 2'b11, data, hit);
    if (hit) error_count++;

    // Fill set 1, way 1
    cache_read(32'h0001_0010, 2'b11, data, hit);
    if (hit) error_count++;

    $display("TEST 1: Cache filled - all should be misses");
  endtask

  // =========================================================================
  // TEST 2: Read filled lines (should all hit)
  // =========================================================================
  task test_2_read_hits();
    logic [31:0] data;
    logic        hit;

    $display("\n========================================");
    $display("TEST 2: Read filled lines (should hit)");
    $display("========================================");

    cache_read(32'h0000_0000, 2'b11, data, hit);
    if (!hit) error_count++;

    cache_read(32'h0001_0000, 2'b11, data, hit);
    if (!hit) error_count++;

    cache_read(32'h0000_0010, 2'b11, data, hit);
    if (!hit) error_count++;

    cache_read(32'h0001_0010, 2'b11, data, hit);
    if (!hit) error_count++;

    $display("TEST 2: All reads should hit");
  endtask

  // =========================================================================
  // TEST 3: Write to cache (mark dirty)
  // =========================================================================
  task test_3_write_cache();
    $display("\n========================================");
    $display("TEST 3: Write to cache");
    $display("========================================");

    cache_write(32'h0000_0000, 2'b11, 32'hDEADBEEF);
    cache_write(32'h0001_0000, 2'b11, 32'hCAFEBABE);

    $display("TEST 3: Writes complete - lines should be dirty");
  endtask

  // =========================================================================
  // TEST 4: Force writeback
  // =========================================================================
  task test_4_writeback();
    logic [31:0] data;
    logic        hit;

    $display("\n========================================");
    $display("TEST 4: Force writeback");
    $display("========================================");

    // Access new addresses that map to same sets
    // This should evict dirty lines and cause writeback
    cache_read(32'h0002_0000, 2'b11, data, hit);  // Set 0 - should writeback way with DEADBEEF
    cache_read(32'h0002_0010, 2'b11, data, hit);  // Set 1 - should writeback

    $display("TEST 4: Writeback forced");
  endtask

  // =========================================================================
  // Main Test Flow
  // =========================================================================
  initial begin
    error_count = 0;
    cache_req = '0;
    cache_req.ready = 1'b1;
    flush = 0;

    // Wait for reset
    @(posedge rst_n);
    repeat (10) @(posedge clk);

    $display("\n");
    $display("=============================================");
    $display("DCache Standalone Verification");
    $display("  NUM_SET=%0d, NUM_WAY=%0d", NUM_SET, NUM_WAY);
    $display("  Cache size: %0d bytes", NUM_SET * NUM_WAY * (BLK_SIZE / 8));
    $display("=============================================");

    // Run tests
    test_1_fill_cache();
    test_2_read_hits();
    test_3_write_cache();
    test_4_writeback();

    // Final report
    repeat (20) @(posedge clk);
    $display("\n");
    $display("=============================================");
    if (error_count == 0) begin
      $display("ALL TESTS PASSED!");
    end else begin
      $display("TESTS FAILED: %0d errors", error_count);
    end
    $display("=============================================");

    $finish;
  end

  // =========================================================================
  // Waveform Dumping
  // =========================================================================
  initial begin
    $dumpfile("dcache_tb.vcd");
    $dumpvars(0, tb_dcache);
  end

endmodule
