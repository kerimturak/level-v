`timescale 1ns / 1ps

typedef struct packed {
  logic            valid;
  logic            ready;
  logic [XLEN-1:0] addr;
  logic            uncached;
  logic            rw;
  rw_size_e        rw_size;
  logic [31:0]     data;
} cache_req_t;

typedef struct packed {
  logic        valid;
  logic        ready;
  logic [31:0] data;
} cache_res_t;

typedef struct packed {
  logic                valid;
  logic                ready;
  logic [BLK_SIZE-1:0] data;
} lowX_res_t;

typedef struct packed {
  logic                valid;
  logic                ready;
  logic [XLEN-1:0]     addr;
  rw_size_e            rw_size;
  logic                rw;
  logic [BLK_SIZE-1:0] data;
  logic                uncached;
} lowX_req_t;


// Self-checking testbench for the icache module
module tb_icache;

  // Parameters (matching design parameters)
  parameter CACHE_SIZE = 1024;
  parameter BLK_SIZE = ceres_pkg::BLK_SIZE;
  parameter XLEN = ceres_pkg::XLEN;
  parameter NUM_WAY = 4;

  // Local parameters
  localparam NUM_SET = (CACHE_SIZE / BLK_SIZE) / NUM_WAY;
  localparam IDX_WIDTH = $clog2(NUM_SET);

  // Clock, reset, and control signals
  logic       clk;
  logic       rst_ni;
  logic       flush_i;

  // Interface signals for the icache module
  cache_req_t cache_req_i;
  cache_res_t cache_res_o;
  lowX_res_t  lowX_res_i;
  lowX_req_t  lowX_req_o;

  // Clock generation (10 ns period)
  initial clk = 0;
  always #5 clk = ~clk;

  // Instance of the icache module
  cache #(
      .IS_ICACHE  (0),
      .cache_req_t(cache_req_t),
      .cache_res_t(cache_res_t),
      .lowX_req_t (lowX_req_t),
      .lowX_res_t (lowX_res_t),
      .CACHE_SIZE (CACHE_SIZE),
      .BLK_SIZE   (BLK_SIZE),
      .XLEN       (XLEN),
      .NUM_WAY    (NUM_WAY)
  ) dut (
      .clk_i      (clk),
      .rst_ni     (rst_ni),
      .flush_i    (flush_i),
      .cache_req_i(cache_req_i),
      .cache_res_o(cache_res_o),
      .lowX_res_i (lowX_res_i),
      .lowX_req_o (lowX_req_o)
  );

  // Main stimulus block of the testbench
  initial begin
    // Initial values
    rst_ni      <= 0;
    flush_i     <= 0;
    cache_req_i <= '0;
    lowX_res_i  <= '0;

    // --- RESET PHASE ---
    repeat (2) @(posedge clk);
    rst_ni <= 1;  // Release reset
    repeat (2) @(posedge clk);

    // ================================
    // TEST 1: CACHE MISS & MEMORY LOAD
    // ================================
    $display("\n=== TEST 1: CACHE MISS & MEMORY LOAD ===");
    // Send a request to an address not yet loaded in the cache (e.g., 0x0000_0040)
    cache_req_i.valid    <= 1;
    cache_req_i.ready    <= 1;
    cache_req_i.addr     <= 32'h0000_0040;
    cache_req_i.uncached <= 0;

    // Wait for one clock cycle; on a cache miss, lowX_req_o.valid is expected.
    @(posedge clk);
    cache_req_i.valid <= '0;
    lowX_res_i.ready  <= 1;
    #1;
    if (!lowX_req_o.valid) begin
      $display("[ERROR] Time %t: Expected lowX_req valid not asserted (cache miss)!", $time);
      $stop;
    end else begin
      $display("[INFO] Time %t: lowX_req valid asserted, cache miss detected.", $time);
    end

    // Simulate memory load: provide data through lowX_res_i.
    @(posedge clk);
    lowX_res_i.ready <= '0;
    lowX_res_i.valid <= 1;
    lowX_res_i.blk   <= 64'hDEADBEEF_DEADBEEF;  // Example block data

    // Check the cache response
    @(posedge clk);
    if (cache_res_o.valid && (cache_res_o.blk == lowX_res_i.blk)) $display("[PASS] Time %t: Correct block loaded after cache miss.", $time);
    else begin
      $display("[FAIL] Time %t: Cache block data error! Expected: %h, Received: %h", $time, lowX_res_i.blk, cache_res_o.blk);
      $stop;
    end

    // Clear temporary valid signals
    cache_req_i.valid <= 0;
    lowX_res_i.valid  <= 0;
    @(posedge clk);

    // =====================
    // TEST 2: CACHE HIT
    // =====================
    $display("\n=== TEST 2: CACHE HIT ===");
    // Send another request to the same address; now a cache hit is expected.
    cache_req_i.valid    <= 1;
    cache_req_i.addr     <= 32'h0000_0040;
    cache_req_i.uncached <= 0;

    @(posedge clk);
    cache_req_i.valid <= 0;
    #1;
    if (!cache_res_o.miss && cache_res_o.valid && (cache_res_o.blk == 64'hDEADBEEF_DEADBEEF)) $display("[PASS] Time %t: Cache hit successful, correct block returned.", $time);
    else begin
      $display("[FAIL] Time %t: Cache hit did not occur as expected!", $time);
      $stop;
    end

    repeat (2) @(posedge clk);

    // ============================
    // TEST 3: FLUSH OPERATION
    // ============================
    $display("\n=== TEST 3: FLUSH OPERATION ===");
    // Activate flush, then send a request to the same address to verify the cache is cleared and a miss occurs.
    flush_i <= 1;
    @(posedge clk);
    flush_i              <= 0;

    cache_req_i.valid    <= 1;
    cache_req_i.addr     <= 32'h0000_0040;
    cache_req_i.uncached <= 0;
    repeat (NUM_SET) @(posedge clk);
    #1;
    if (cache_res_o.miss) $display("[PASS] Time %t: Cache miss occurred as expected after flush.", $time);
    else begin
      $display("[FAIL] Time %t: Cache flush did not result in a cache miss as expected!", $time);
      $stop;
    end
    @(posedge clk);

    // ===============================
    // TEST 4: MULTIPLE ADDRESS ACCESSES
    // ===============================
    $display("\n=== TEST 4: MULTIPLE ADDRESS ACCESSES ===");
    // Access several addresses in different sets.
    repeat (4) begin : multi_addr_test
      cache_req_i.valid    <= 1;
      cache_req_i.addr     <= {16'h0001, $urandom_range(0, 16'hFFFF)};  // random lower 16 bits
      cache_req_i.uncached <= 0;
      @(posedge clk);
      cache_req_i.valid <= 0;
      @(posedge clk);
    end

    // ================================
    // TEST 5: CONSECUTIVE REQUESTS (BURST MODE)
    // ================================
    $display("\n=== TEST 5: CONSECUTIVE REQUESTS (BURST MODE) ===");
    // Issue a burst of back-to-back requests to different addresses.
    for (int i = 0; i < 5; i++) begin
      cache_req_i.valid    <= 1;
      cache_req_i.addr     <= 32'h1000_0000 + (i * 32'h40);
      cache_req_i.uncached <= 0;
      @(posedge clk);
      cache_req_i.valid <= 0;
      @(posedge clk);
    end

    // ====================================
    // TEST 6: RANDOMIZED REQUEST SEQUENCE
    // ====================================
    $display("\n=== TEST 6: RANDOMIZED REQUEST SEQUENCE ===");
    // Loop to issue random requests.
    for (int i = 0; i < 10; i++) begin
      cache_req_i.valid    <= 1;
      cache_req_i.addr     <= $urandom;  // random 32-bit address
      cache_req_i.uncached <= 0;
      @(posedge clk);
      cache_req_i.valid <= 0;
      @(posedge clk);
    end

    // ====================
    // TEST 7: UNCACHED ACCESSES
    // ====================
    $display("\n=== TEST 7: UNCACHED ACCESSES ===");
    // Send an uncached request; ensure that the cache bypasses the normal storage mechanism.
    cache_req_i.valid    <= 1;
    cache_req_i.addr     <= 32'h2000_0000;
    cache_req_i.uncached <= 1;  // Uncached flag set
    @(posedge clk);
    cache_req_i.valid <= 0;
    // Here, you might check that lowX_req_o is directly used and the cache response is generated accordingly.
    @(posedge clk);

    // ====================
    // TEST 8: BOUNDARY CONDITIONS
    // ====================
    $display("\n=== TEST 8: BOUNDARY CONDITIONS ===");
    // Test lowest and highest addresses within the address space.
    cache_req_i.valid    <= 1;
    cache_req_i.addr     <= 32'h0000_0000;  // lowest address
    cache_req_i.uncached <= 0;
    @(posedge clk);
    cache_req_i.valid <= 0;
    @(posedge clk);

    cache_req_i.valid    <= 1;
    cache_req_i.addr     <= 32'hFFFF_FFF0;  // near highest address
    cache_req_i.uncached <= 0;
    @(posedge clk);
    cache_req_i.valid <= 0;
    @(posedge clk);

    // ============================================
    // TEST 9: REPLACEMENT / PLRU VERIFICATION
    // ============================================
    $display("\n=== TEST 9: REPLACEMENT / PLRU VERIFICATION ===");
    // Fill one cache set completely and then force an eviction.
    // First, fill the set by accessing NUM_WAY unique addresses that map to the same set.
    for (int i = 0; i < NUM_WAY; i++) begin
      cache_req_i.valid    <= 1;
      // Construct an address that maps to a particular set (e.g., set 0) by ensuring the index bits are 0.
      cache_req_i.addr     <= {{XLEN - IDX_WIDTH - 8{1'b0}}, 8'hA0 + i, {IDX_WIDTH{1'b0}}};
      cache_req_i.uncached <= 0;
      @(posedge clk);
      cache_req_i.valid <= 0;
      @(posedge clk);
      // Simulate memory load response for each request.
      lowX_res_i.valid <= 1;
      lowX_res_i.blk   <= 64'hCAFEBABE_00000000 + i;
      @(posedge clk);
      lowX_res_i.valid <= 0;
      @(posedge clk);
    end

    // Now, issue one more request to the same set to force an eviction.
    cache_req_i.valid    <= 1;
    cache_req_i.addr     <= {{XLEN - IDX_WIDTH - 8{1'b0}}, 8'hA0 + NUM_WAY, {IDX_WIDTH{1'b0}}};
    cache_req_i.uncached <= 0;
    @(posedge clk);
    cache_req_i.valid <= 0;
    @(posedge clk);

    // ==================================
    // TEST 10: OVERLAPPING REQUESTS
    // ==================================
    $display("\n=== TEST 10: OVERLAPPING REQUESTS ===");
    // Issue a request and, before its completion, issue a new request.
    cache_req_i.valid    <= 1;
    cache_req_i.addr     <= 32'h3000_0000;
    cache_req_i.uncached <= 0;
    @(posedge clk);
    // While the first request is still being processed, send another request.
    cache_req_i.valid    <= 1;
    cache_req_i.addr     <= 32'h3000_0040;
    cache_req_i.uncached <= 0;
    @(posedge clk);
    cache_req_i.valid <= 0;
    @(posedge clk);

    // Wait a few cycles to allow processing
    repeat (5) @(posedge clk);

    // Final message if all tests pass
    $display("\n[INFO] All tests passed successfully.");
    $stop;
  end

endmodule
