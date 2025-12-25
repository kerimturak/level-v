// =============================================================================
// Comprehensive DCache Test - All Sizes, Random Access Patterns
// =============================================================================
// Tests:
// - Byte (2'b01), Half (2'b10), Word (2'b11) accesses
// - Aligned and unaligned addresses
// - Random read/write patterns
// - Cache fills, hits, misses, evictions, writebacks
// - Verify data integrity after each operation
// =============================================================================

`timescale 1ns/1ps

module tb_dcache_comprehensive;

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
    repeat(5) @(posedge clk);
    rst_n = 1;
  end

  always @(posedge clk) begin
    if (rst_n) cycle_count++;
  end

  // Interfaces
  dcache_req_t cache_req;
  dcache_res_t cache_res;
  dlowX_req_t  lowx_req;
  dlowX_res_t  lowx_res;
  logic flush;

  // Memory model (64KB)
  logic [7:0] memory [65536];
  logic [127:0] mem_rdata;

  // Shadow memory to track expected values
  logic [7:0] shadow_mem [65536];

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      lowx_res.valid <= 0;
      lowx_res.data <= '0;
      for (int i = 0; i < 65536; i++) begin
        memory[i] <= i[7:0];
        shadow_mem[i] <= i[7:0];
      end
    end else begin
      lowx_res.valid <= 0;
      if (lowx_req.valid) begin
        lowx_res.valid <= 1;
        if (lowx_req.rw) begin
          // Memory write
          for (int i = 0; i < 16; i++)
            memory[lowx_req.addr[15:0] + i] <= lowx_req.data[i*8 +: 8];
          $display("[C%0d] MEM WR: addr=0x%h data=0x%h",
            cycle_count, lowx_req.addr, lowx_req.data);
        end else begin
          // Memory read
          for (int i = 0; i < 16; i++)
            mem_rdata[i*8 +: 8] = memory[lowx_req.addr[15:0] + i];
          lowx_res.data <= mem_rdata;
          $display("[C%0d] MEM RD: addr=0x%h data=0x%h",
            cycle_count, lowx_req.addr, mem_rdata);
        end
      end
    end
  end

  assign lowx_req.ready = 1;
  assign lowx_res.ready = 1;

  // DUT
  dcache #(
    .cache_req_t (dcache_req_t),
    .cache_res_t (dcache_res_t),
    .lowX_req_t  (dlowX_req_t),
    .lowX_res_t  (dlowX_res_t),
    .CACHE_SIZE  (512),
    .BLK_SIZE    (128),
    .XLEN        (32),
    .NUM_WAY     (2)
  ) dut (
    .clk_i          (clk),
    .rst_ni         (rst_n),
    .flush_i        (flush),
    .cache_req_i    (cache_req),
    .cache_res_o    (cache_res),
    .lowX_res_i     (lowx_res),
    .lowX_req_o     (lowx_req),
    .fencei_stall_o ()
  );

  // =========================================================================
  // Helper Tasks
  // =========================================================================

  // Update shadow memory for expected values
  task update_shadow(input logic [31:0] addr, input logic [1:0] size, input logic [31:0] data);
    case (size)
      2'b01: begin  // Byte
        shadow_mem[addr[15:0]] = data[7:0];
      end
      2'b10: begin  // Half
        shadow_mem[addr[15:0]] = data[7:0];
        shadow_mem[addr[15:0]+1] = data[15:8];
      end
      2'b11: begin  // Word
        shadow_mem[addr[15:0]] = data[7:0];
        shadow_mem[addr[15:0]+1] = data[15:8];
        shadow_mem[addr[15:0]+2] = data[23:16];
        shadow_mem[addr[15:0]+3] = data[31:24];
      end
    endcase
  endtask

  // Get expected value from shadow memory
  function logic [31:0] get_expected(input logic [31:0] addr, input logic [1:0] size);
    logic [31:0] result;
    result = '0;
    case (size)
      2'b01: begin  // Byte
        result[7:0] = shadow_mem[addr[15:0]];
      end
      2'b10: begin  // Half
        result[7:0] = shadow_mem[addr[15:0]];
        result[15:8] = shadow_mem[addr[15:0]+1];
      end
      2'b11: begin  // Word
        result[7:0] = shadow_mem[addr[15:0]];
        result[15:8] = shadow_mem[addr[15:0]+1];
        result[23:16] = shadow_mem[addr[15:0]+2];
        result[31:24] = shadow_mem[addr[15:0]+3];
      end
    endcase
    return result;
  endfunction

  // Cache read operation
  task cache_read(
    input logic [31:0] addr,
    input logic [1:0] size,
    input string size_str
  );
    logic [31:0] read_data, expected_data;

    @(posedge clk);
    while (cache_res.valid) @(posedge clk);

    cache_req.valid <= 1;
    cache_req.addr <= addr;
    cache_req.rw <= 0;
    cache_req.rw_size <= rw_size_e'(size);
    cache_req.uncached <= 0;
    cache_req.data <= '0;
    cache_req.ready <= 1;

    wait(cache_res.valid);
    read_data = cache_res.data;

    @(posedge clk);
    cache_req.valid <= 0;
    while (cache_res.valid) @(posedge clk);

    // Mask read data based on size (dcache returns word-aligned data)
    // For byte/half, we need to extract the correct portion based on address
    case (size)
      2'b01: begin // BYTE
        case (addr[1:0])
          2'd0: read_data = {24'h0, read_data[7:0]};
          2'd1: read_data = {24'h0, read_data[15:8]};
          2'd2: read_data = {24'h0, read_data[23:16]};
          2'd3: read_data = {24'h0, read_data[31:24]};
        endcase
      end
      2'b10: begin // HALF
        read_data = addr[1] ? {16'h0, read_data[31:16]} : {16'h0, read_data[15:0]};
      end
      2'b11: begin // WORD - no masking needed
        read_data = read_data;
      end
    endcase

    // Get expected value from shadow memory
    expected_data = get_expected(addr, size);

    // Verify data
    if (read_data !== expected_data) begin
      $error("[T%0d] READ MISMATCH! addr=0x%h size=%s got=0x%h expected=0x%h",
        test_count, addr, size_str, read_data, expected_data);
      error_count++;
    end else begin
      $display("[T%0d] ✓ RD addr=0x%h %s data=0x%h",
        test_count, addr, size_str, read_data);
    end
    test_count++;
  endtask

  // Cache write operation
  task cache_write(
    input logic [31:0] addr,
    input logic [1:0] size,
    input logic [31:0] data,
    input string size_str
  );
    @(posedge clk);
    while (cache_res.valid) @(posedge clk);

    cache_req.valid <= 1;
    cache_req.addr <= addr;
    cache_req.rw <= 1;
    cache_req.rw_size <= rw_size_e'(size);
    cache_req.data <= data;
    cache_req.uncached <= 0;
    cache_req.ready <= 1;

    wait(cache_res.valid);

    @(posedge clk);
    cache_req.valid <= 0;
    while (cache_res.valid) @(posedge clk);

    // Update shadow memory
    update_shadow(addr, size, data);

    $display("[T%0d] ✓ WR addr=0x%h %s data=0x%h",
      test_count, addr, size_str, data);
    test_count++;
  endtask

  // =========================================================================
  // Main Test Sequence
  // =========================================================================

  initial begin
    error_count = 0;
    test_count = 0;
    cache_req = '0;
    cache_req.ready = 1;
    flush = 0;

    @(posedge rst_n);
    repeat(10) @(posedge clk);

    $display("\n========================================");
    $display("COMPREHENSIVE DCACHE TEST");
    $display("Cache: 512 bits = 2 sets x 2 ways x 128 bits");
    $display("Testing: Byte/Half/Word, Aligned/Unaligned");
    $display("========================================\n");

    // =====================================================================
    // TEST GROUP 1: Sequential access - all sizes, aligned
    // =====================================================================
    $display("\n=== TEST 1: Sequential Aligned Access ===");

    // Word accesses (aligned to 4-byte boundaries)
    cache_read(32'h0000, 2'b11, "WORD");  // Cold miss
    cache_read(32'h0004, 2'b11, "WORD");  // Same line, should hit
    cache_read(32'h0008, 2'b11, "WORD");
    cache_read(32'h000C, 2'b11, "WORD");

    // Half accesses (aligned to 2-byte boundaries)
    cache_read(32'h0100, 2'b10, "HALF");  // Cold miss, different line
    cache_read(32'h0102, 2'b10, "HALF");  // Same line, hit
    cache_read(32'h0104, 2'b10, "HALF");
    cache_read(32'h0106, 2'b10, "HALF");

    // Byte accesses (any address)
    cache_read(32'h0200, 2'b01, "BYTE");  // Cold miss
    cache_read(32'h0201, 2'b01, "BYTE");  // Same line, hit
    cache_read(32'h0202, 2'b01, "BYTE");
    cache_read(32'h0203, 2'b01, "BYTE");

    // =====================================================================
    // TEST GROUP 2: Write then read - verify data integrity
    // =====================================================================
    $display("\n=== TEST 2: Write-Read Verification ===");

    // Write words
    cache_write(32'h1000, 2'b11, 32'hDEADBEEF, "WORD");
    cache_write(32'h1004, 2'b11, 32'hCAFEBABE, "WORD");

    // Read back
    cache_read(32'h1000, 2'b11, "WORD");
    cache_read(32'h1004, 2'b11, "WORD");

    // Write halfs
    cache_write(32'h2000, 2'b10, 32'h1234, "HALF");
    cache_write(32'h2002, 2'b10, 32'h5678, "HALF");

    // Read back
    cache_read(32'h2000, 2'b10, "HALF");
    cache_read(32'h2002, 2'b10, "HALF");

    // Write bytes
    cache_write(32'h3000, 2'b01, 32'hAA, "BYTE");
    cache_write(32'h3001, 2'b01, 32'hBB, "BYTE");
    cache_write(32'h3002, 2'b01, 32'hCC, "BYTE");
    cache_write(32'h3003, 2'b01, 32'hDD, "BYTE");

    // Read back
    cache_read(32'h3000, 2'b01, "BYTE");
    cache_read(32'h3001, 2'b01, "BYTE");
    cache_read(32'h3002, 2'b01, "BYTE");
    cache_read(32'h3003, 2'b01, "BYTE");

    // =====================================================================
    // TEST GROUP 3: Unaligned access
    // =====================================================================
    $display("\n=== TEST 3: Unaligned Access ===");

    // Unaligned word (addr not multiple of 4)
    cache_write(32'h4001, 2'b11, 32'h11223344, "WORD");
    cache_read(32'h4001, 2'b11, "WORD");

    // Unaligned half (addr not multiple of 2)
    cache_write(32'h5001, 2'b10, 32'h5566, "HALF");
    cache_read(32'h5001, 2'b10, "HALF");

    // =====================================================================
    // TEST GROUP 4: Mixed size access to same location
    // =====================================================================
    $display("\n=== TEST 4: Mixed Size Access ===");

    // Write word
    cache_write(32'h6000, 2'b11, 32'hAABBCCDD, "WORD");

    // Read as bytes
    cache_read(32'h6000, 2'b01, "BYTE");  // Should be 0xDD
    cache_read(32'h6001, 2'b01, "BYTE");  // Should be 0xCC
    cache_read(32'h6002, 2'b01, "BYTE");  // Should be 0xBB
    cache_read(32'h6003, 2'b01, "BYTE");  // Should be 0xAA

    // Read as halfs
    cache_read(32'h6000, 2'b10, "HALF");  // Should be 0xCCDD
    cache_read(32'h6002, 2'b10, "HALF");  // Should be 0xAABB

    // =====================================================================
    // TEST GROUP 5: Cache eviction and writeback
    // =====================================================================
    $display("\n=== TEST 5: Eviction & Writeback ===");

    // Fill all 4 cache lines with dirty data
    cache_write(32'h0000, 2'b11, 32'h00001111, "WORD");  // Set 0, way 0
    cache_write(32'h10000, 2'b11, 32'h00002222, "WORD"); // Set 0, way 1
    cache_write(32'h0010, 2'b11, 32'h00003333, "WORD");  // Set 1, way 0
    cache_write(32'h10010, 2'b11, 32'h00004444, "WORD"); // Set 1, way 1

    // Force eviction by accessing new tags
    cache_read(32'h20000, 2'b11, "WORD");  // Evict set 0
    cache_read(32'h20010, 2'b11, "WORD");  // Evict set 1

    // Read back original addresses - should cause fills from memory
    cache_read(32'h0000, 2'b11, "WORD");   // Should have 0x00001111
    cache_read(32'h10000, 2'b11, "WORD");  // Should have 0x00002222

    // =====================================================================
    // TEST GROUP 6: Random stress test (limited address range)
    // =====================================================================
    $display("\n=== TEST 6: Random Stress Test (256 byte range) ===");
    $display("Address range: 0x7000-0x70FF (4x cache size for evictions)");

    for (int i = 0; i < 100; i++) begin
      logic [31:0] addr, data;
      logic [1:0] size;
      logic rw;
      string size_str;
      int offset;

      // Random offset within 256-byte range (0x7000-0x70FF)
      // This is 4x cache size (64 bytes), enough to cause evictions
      offset = $urandom_range(0, 255);
      addr = 32'h7000 + offset;

      // Random size: byte (2'b01), half (2'b10), or word (2'b11)
      case ($urandom_range(0, 2))
        0: begin
          size = 2'b01;
          size_str = "BYTE";
          // Byte can be at any address
        end
        1: begin
          size = 2'b10;
          size_str = "HALF";
          addr[0] = 0;  // Align to 2-byte boundary
        end
        2: begin
          size = 2'b11;
          size_str = "WORD";
          addr[1:0] = 2'b00;  // Align to 4-byte boundary
        end
      endcase

      // Random read or write (60% read, 40% write)
      rw = ($urandom_range(0, 9) < 4);

      if (rw) begin
        data = $urandom;
        cache_write(addr, size, data, size_str);
      end else begin
        cache_read(addr, size, size_str);
      end

      // Occasionally add some delay
      if (i % 10 == 9) repeat(2) @(posedge clk);
    end

    // =====================================================================
    // Final Report
    // =====================================================================
    repeat(20) @(posedge clk);
    $display("\n========================================");
    $display("TEST COMPLETE");
    $display("  Total tests: %0d", test_count);
    $display("  Errors: %0d", error_count);
    if (error_count == 0) begin
      $display("  ✓✓✓ ALL TESTS PASSED! ✓✓✓");
    end else begin
      $display("  ✗✗✗ TESTS FAILED! ✗✗✗");
    end
    $display("========================================\n");

    $finish;
  end

  // Waveform
  initial begin
    $dumpfile("comprehensive.vcd");
    $dumpvars(0, tb_dcache_comprehensive);
  end

endmodule
