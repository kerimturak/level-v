// =============================================================================
// Detailed DCache Test with Cycle-by-Cycle Checking
// =============================================================================
// Tests each operation with backdoor array checking

`timescale 1ns / 1ps

module tb_dcache_detailed;

  import ceres_param::*;

  logic clk, rst_n;
  int cycle_count;

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

  // Memory
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
          $display("[C%0d] MEM WR: addr=0x%h", cycle_count, lowx_req.addr);
        end else begin
          for (int i = 0; i < 16; i++) mem_rdata[i*8+:8] = memory[lowx_req.addr[15:0]+i];
          lowx_res.data <= mem_rdata;
          $display("[C%0d] MEM RD: addr=0x%h data=0x%h", cycle_count, lowx_req.addr, mem_rdata);
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

  // =========================================================================
  // Backdoor Monitoring
  // =========================================================================

  task automatic display_cache_state(string msg);
    $display("\n[C%0d] ========== %s ==========", cycle_count, msg);

    // Access DUT internal arrays via hierarchical reference
    $display("[C%0d] Cache State:", cycle_count);

    // Valid & Hit vectors
    $display("  valid_vec = %b, hit_vec = %b, miss = %b", dut.cache_valid_vec, dut.cache_hit_vec, dut.cache_miss);

    // Tag array (2 sets x 2 ways)
    for (int s = 0; s < 2; s++) begin
      $display("  Set %0d:", s);
      for (int w = 0; w < 2; w++) begin
        // Tag SRAM output
        // TAG_SIZE = 32 - 1 - 4 = 27 for 2-set cache
        // Tag array stores [27:0] where bit [27] = valid, bits [26:0] = tag
        $display("    Way %0d: valid=%b tag=0x%h dirty=%b", w, dut.tsram.rtag[w][27],  // valid bit at TAG_SIZE
                 dut.tsram.rtag[w][26:0],  // tag bits [TAG_SIZE-1:0]
                 dut.dirty_reg[s][w]  // dirty bit from register
        );
      end
      $display("    PLRU node = %b", dut.node_q[s]);
    end

    $display("[C%0d] ==========================================\n", cycle_count);
  endtask

  task automatic check_tag_written(int set_idx, int way, logic [18:0] expected_tag);
    logic [19:0] actual_tag_entry;
    logic        actual_valid;
    logic [18:0] actual_tag;

    // Read tag array - need to access storage array directly
    // For sp_bram, we'd need to know internal structure
    // For now, check via read path

    $display("[C%0d] CHECK: Tag write to set=%0d way=%0d", cycle_count, set_idx, way);
    $display("       Expected: valid=1 tag=0x%05h", expected_tag);

    // Note: Tag will be visible in next read cycle
    // We can't directly read BRAM contents without knowing its internals
  endtask

  // =========================================================================
  // Test Sequence
  // =========================================================================

  initial begin
    cache_req = '0;
    cache_req.ready = 1;
    flush = 0;

    @(posedge rst_n);
    repeat (5) @(posedge clk);

    $display("\n========================================");
    $display("DETAILED DCACHE TEST");
    $display("========================================\n");

    display_cache_state("Initial State");

    // =====================================================================
    // TEST 1: First Read - Cold Miss to Set 0
    // =====================================================================
    $display("[C%0d] TEST 1: Cold miss - Read addr=0x1000 (set=0)", cycle_count);

    @(posedge clk);
    cache_req.valid <= 1;
    cache_req.addr <= 32'h0000_1000;  // Bit 4 = 0 → set 0
    cache_req.rw <= 0;
    cache_req.rw_size <= WORD;  // Word (32-bit)

    // Cycle 0→1: Request issued, arrays being read
    @(posedge clk);
    $display("[C%0d] Cycle 1: Arrays read, hit/miss detection", cycle_count);
    display_cache_state("After Cycle 1");

    // Wait for response
    wait (cache_res.valid);
    $display("[C%0d] Response: data=0x%h miss=%b", cycle_count, cache_res.data, cache_res.miss);

    @(posedge clk);
    cache_req.valid <= 0;

    // Check: Should be MISS, should trigger fill
    if (cache_res.miss != 1) $error("Expected MISS!");

    repeat (3) @(posedge clk);
    display_cache_state("After Fill");

    // =====================================================================
    // TEST 2: Re-read Same Address - Should HIT
    // =====================================================================
    $display("[C%0d] TEST 2: Re-read 0x1000 - expect HIT", cycle_count);

    @(posedge clk);
    cache_req.valid <= 1;
    cache_req.addr <= 32'h0000_1000;
    cache_req.rw <= 0;
    cache_req.rw_size <= WORD;  // Word (32-bit)

    wait (cache_res.valid);
    $display("[C%0d] Response: data=0x%h miss=%b", cycle_count, cache_res.data, cache_res.miss);

    if (cache_res.miss != 0) $error("Expected HIT!");
    if (cache_res.data !== 32'h03020100) $error("Wrong data! Expected 0x03020100, got 0x%h", cache_res.data);

    @(posedge clk);
    cache_req.valid <= 0;

    repeat (3) @(posedge clk);
    display_cache_state("After Hit");

    // =====================================================================
    // TEST 3: Different Tag, Same Set - Should MISS and Evict
    // =====================================================================
    $display("[C%0d] TEST 3: Read addr=0x11000 (set=0, different tag) - expect MISS", cycle_count);

    @(posedge clk);
    cache_req.valid <= 1;
    cache_req.addr <= 32'h0001_1000;  // Different tag, same set
    cache_req.rw <= 0;
    cache_req.rw_size <= WORD;  // Word (32-bit)

    wait (cache_res.valid);
    $display("[C%0d] Response: data=0x%h miss=%b", cycle_count, cache_res.data, cache_res.miss);

    if (cache_res.miss != 1) $error("Expected MISS (tag mismatch)!");

    @(posedge clk);
    cache_req.valid <= 0;

    repeat (3) @(posedge clk);
    display_cache_state("After Tag Miss");

    // =====================================================================
    // TEST 4: Write to Create Dirty Line
    // =====================================================================
    $display("[C%0d] TEST 4: Write to 0x1000 - mark dirty", cycle_count);

    @(posedge clk);
    cache_req.valid <= 1;
    cache_req.addr <= 32'h0000_1000;
    cache_req.rw <= 1;
    cache_req.rw_size <= WORD;  // Word (32-bit)
    cache_req.data <= 32'hDEAD_BEEF;

    wait (cache_res.valid);
    $display("[C%0d] Write complete", cycle_count);

    @(posedge clk);
    cache_req.valid <= 0;

    repeat (3) @(posedge clk);
    display_cache_state("After Write (should be dirty)");

    // =====================================================================
    // TEST 5: Evict Dirty Line - Should Writeback
    // =====================================================================
    $display("[C%0d] TEST 5: Read 0x21000 - will evict way-1 (clean)", cycle_count);

    @(posedge clk);
    cache_req.valid <= 1;
    cache_req.addr <= 32'h0002_1000;  // Different tag, will evict way-1
    cache_req.rw <= 0;
    cache_req.rw_size <= WORD;  // Word (32-bit)

    wait (cache_res.valid);
    $display("[C%0d] Response: data=0x%h miss=%b", cycle_count, cache_res.data, cache_res.miss);

    @(posedge clk);
    cache_req.valid <= 0;

    repeat (3) @(posedge clk);
    display_cache_state("After Clean Eviction");

    // Now force eviction of dirty way-0
    $display("[C%0d] TEST 6: Read 0x31000 - will evict way-0 (dirty), expect writeback", cycle_count);

    @(posedge clk);
    cache_req.valid <= 1;
    cache_req.addr <= 32'h0003_1000;  // Different tag, will evict way-0 (dirty!)
    cache_req.rw <= 0;
    cache_req.rw_size <= WORD;  // Word (32-bit)

    wait (cache_res.valid);
    $display("[C%0d] Response after writeback+fill: data=0x%h miss=%b", cycle_count, cache_res.data, cache_res.miss);

    @(posedge clk);
    cache_req.valid <= 0;

    repeat (5) @(posedge clk);
    display_cache_state("After Dirty Writeback+Fill");

    // Check memory - should have DEADBEEF written back
    $display("Memory at 0x1000: 0x%h %h %h %h (expected: ef be ad de)", memory[32'h1003], memory[32'h1002], memory[32'h1001], memory[32'h1000]);

    if (memory[32'h1000] !== 8'hef || memory[32'h1001] !== 8'hbe || memory[32'h1002] !== 8'had || memory[32'h1003] !== 8'hde) begin
      $error("Writeback data incorrect in memory!");
      $display("  Got: 0x%h%h%h%h, Expected: 0xdeadbeef", memory[32'h1003], memory[32'h1002], memory[32'h1001], memory[32'h1000]);
    end else begin
      $display("Writeback verified in memory: 0x%h%h%h%h", memory[32'h1003], memory[32'h1002], memory[32'h1001], memory[32'h1000]);
    end

    repeat (10) @(posedge clk);
    $display("\n========================================");
    $display("DETAILED TEST COMPLETE");
    $display("========================================\n");
    $finish;
  end

  // Waveform
  initial begin
    $dumpfile("detailed.vcd");
    $dumpvars(0, tb_dcache_detailed);
  end

endmodule
