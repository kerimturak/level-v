`timescale 1ns / 1ps

module tb_dcache_simple;
  import ceres_param::*;

  // Parameters - 4-way 2KB config
  localparam int DC_WAY_TB = 4;
  localparam int DC_CAPACITY_TB = 2 * 1024 * 8;
  localparam int BLK_SIZE_TB = 128;
  localparam int XLEN_TB = 32;

  // Clock and reset
  logic clk = 0;
  logic rst_n;

  // DCache interfaces
  ceres_param::dcache_req_t cache_req;
  ceres_param::dcache_res_t cache_res;
  ceres_param::dlowX_req_t lowX_req;
  ceres_param::dlowX_res_t lowX_res;
  logic flush;
  logic fencei_stall;

  // Simple memory model
  logic [7:0] memory [logic [31:0]];
  logic [3:0] mem_delay_cnt;

  // Test statistics
  int load_count = 0;
  int store_count = 0;
  int mismatch_count = 0;
  int total_ops = 0;

  // DCache instance
  dcache #(
      .cache_req_t(ceres_param::dcache_req_t),
      .cache_res_t(ceres_param::dcache_res_t),
      .lowX_res_t(ceres_param::dlowX_res_t),
      .lowX_req_t(ceres_param::dlowX_req_t),
      .CACHE_SIZE(DC_CAPACITY_TB),
      .BLK_SIZE(BLK_SIZE_TB),
      .XLEN(XLEN_TB),
      .NUM_WAY(DC_WAY_TB)
  ) dut (
      .clk_i(clk),
      .rst_ni(rst_n),
      .flush_i(flush),
      .cache_req_i(cache_req),
      .cache_res_o(cache_res),
      .lowX_res_i(lowX_res),
      .lowX_req_o(lowX_req),
      .fencei_stall_o(fencei_stall)
  );

  // Clock generation
  always #5 clk = ~clk;

  // Memory model - responds to lowX requests with 1 cycle delay
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      lowX_res.valid <= 1'b0;
      lowX_res.ready <= 1'b1;
      lowX_res.data <= '0;
      mem_delay_cnt <= 0;
    end else begin
      lowX_res.ready <= 1'b1;

      // Simple 1-cycle delay memory
      if (lowX_req.valid && lowX_res.ready && mem_delay_cnt == 0) begin
        mem_delay_cnt <= 1;
        lowX_res.valid <= 1'b0;

        if (lowX_req.rw) begin
          // Write to memory (cache line = 16 bytes)
          for (int i = 0; i < 16; i++) begin
            memory[lowX_req.addr + i] = lowX_req.data[i*8 +: 8];
          end
        end else begin
          // Read from memory
          for (int i = 0; i < 16; i++) begin
            lowX_res.data[i*8 +: 8] <= memory[lowX_req.addr + i];
          end
        end
      end else if (mem_delay_cnt > 0) begin
        mem_delay_cnt <= 0;
        lowX_res.valid <= 1'b1;
      end else begin
        lowX_res.valid <= 1'b0;
      end
    end
  end

  // Check if address is uncached (Peripheral region: 0x20000000-0x2FFFFFFF)
  function logic is_uncached(input logic [31:0] addr);
    return (addr[31:28] == 4'h2 || addr[31:28] == 4'h3);  // 0x2xxxxxxx or 0x3xxxxxxx
  endfunction

  // Task to perform a store
  task automatic do_store(input logic [31:0] addr, input logic [31:0] data);
    int timeout_cnt;
    begin
      timeout_cnt = 0;

      // Wait for cache to be ready to accept request
      while (!cache_res.ready) begin
        @(posedge clk);
        timeout_cnt++;
        if (timeout_cnt > 100) begin
          $display("ERROR: Cache not ready before store @ 0x%08x", addr);
          $finish;
        end
      end

      @(posedge clk);
      cache_req.valid = 1'b1;
      cache_req.ready = 1'b1;  // CPU ready to accept response
      cache_req.addr = addr;
      cache_req.rw = 1'b1;  // Write
      cache_req.rw_size = 2'b11;  // Word
      cache_req.data = data;
      cache_req.uncached = is_uncached(addr);

      // Wait for cache to respond
      timeout_cnt = 0;
      while (!cache_res.valid) begin
        @(posedge clk);
        timeout_cnt++;
        if (timeout_cnt > 100) begin
          $display("ERROR: Store timeout @ 0x%08x (uncached=%b)", addr, is_uncached(addr));
          $display("  cache_res.valid=%b ready=%b", cache_res.valid, cache_res.ready);
          $display("  lowX_req.valid=%b ready=%b", lowX_req.valid, lowX_res.ready);
          $finish;
        end
      end

      @(posedge clk);
      cache_req.valid = 1'b0;
      store_count++;
    end
  endtask

  // Task to perform a load
  task automatic do_load(input logic [31:0] addr, output logic [31:0] data);
    int timeout_cnt;
    begin
      timeout_cnt = 0;

      // Wait for cache to be ready to accept request
      while (!cache_res.ready) begin
        @(posedge clk);
        timeout_cnt++;
        if (timeout_cnt > 100) begin
          $display("ERROR: Cache not ready before load @ 0x%08x", addr);
          $finish;
        end
      end

      @(posedge clk);
      cache_req.valid = 1'b1;
      cache_req.ready = 1'b1;  // CPU ready to accept response
      cache_req.addr = addr;
      cache_req.rw = 1'b0;  // Read
      cache_req.rw_size = 2'b11;  // Word
      cache_req.uncached = is_uncached(addr);

      // Wait for cache to respond
      timeout_cnt = 0;
      while (!cache_res.valid) begin
        @(posedge clk);
        timeout_cnt++;
        if (timeout_cnt > 100) begin
          $display("ERROR: Load timeout @ 0x%08x (uncached=%b)", addr, is_uncached(addr));
          $display("  cache_res.valid=%b ready=%b", cache_res.valid, cache_res.ready);
          $display("  lowX_req.valid=%b ready=%b", lowX_req.valid, lowX_res.ready);
          $finish;
        end
      end

      data = cache_res.data;

      @(posedge clk);
      cache_req.valid = 1'b0;
      load_count++;
    end
  endtask

  // Test sequence
  initial begin
    int fd;
    string line;
    string op_type;
    logic [31:0] addr, expected_data, read_data;
    int op_count = 0;
    int max_ops = 5000;  // Test first 5000 operations

    // Initialize
    rst_n = 0;
    flush = 0;
    cache_req = '0;

    repeat(10) @(posedge clk);
    rst_n = 1;
    repeat(5) @(posedge clk);

    $display("After reset: cache_res.ready=%b fi_active=%b write_back=%b",
             cache_res.ready, dut.fi_active, dut.write_back);

    // Open memory operations file
    fd = $fopen("/home/kerim/level-v/mem_ops.txt", "r");
    if (fd == 0) begin
      $display("ERROR: Cannot open mem_ops.txt");
      $finish;
    end

    $display("========================================");
    $display("Starting dcache standalone test");
    $display("Config: 4-way, 2KB data cache");
    $display("Testing first %0d operations", max_ops);
    $display("========================================\n");

    // Process each operation
    while (!$feof(fd) && op_count < max_ops) begin
      if ($fgets(line, fd)) begin
        if ($sscanf(line, "%s 0x%h 0x%h", op_type, addr, expected_data) == 3) begin
          total_ops++;

          if (op_type == "load") begin
            do_load(addr, read_data);

            if (read_data !== expected_data) begin
              $display("[MISMATCH %0d] Load @ 0x%08x: expected=0x%08x got=0x%08x",
                       mismatch_count, addr, expected_data, read_data);
              mismatch_count++;

              // Stop after first few mismatches for debugging
              if (mismatch_count >= 10) begin
                $display("\n!!! Stopping after 10 mismatches for analysis !!!");
                break;
              end
            end else if (total_ops % 100 == 0) begin
              $display("[OK %0d] Load @ 0x%08x: data=0x%08x", total_ops, addr, read_data);
            end

          end else if (op_type == "store") begin
            do_store(addr, expected_data);

            if (total_ops % 100 == 0) begin
              $display("[OK %0d] Store @ 0x%08x: data=0x%08x", total_ops, addr, expected_data);
            end
          end

          op_count++;
        end
      end
    end

    $fclose(fd);

    // Final report
    $display("\n========================================");
    $display("Test Results");
    $display("========================================");
    $display("Total operations: %0d", total_ops);
    $display("  Stores: %0d", store_count);
    $display("  Loads:  %0d", load_count);
    $display("  Mismatches: %0d", mismatch_count);
    $display("========================================");

    if (mismatch_count == 0) begin
      $display("✅ TEST PASSED - All operations correct!");
    end else begin
      $display("❌ TEST FAILED - %0d mismatches found", mismatch_count);
    end

    #100;
    $finish;
  end

  // Watchdog timeout
  initial begin
    #50_000_000;  // 50ms timeout
    $display("\n!!! TIMEOUT - Test took too long !!!");
    $display("Completed %0d operations before timeout", total_ops);
    $finish;
  end

endmodule
