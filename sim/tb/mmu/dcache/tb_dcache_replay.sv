`timescale 1ns / 1ps

module tb_dcache_replay;
  import ceres_param::*;

  // Parameters - 4-way 2KB config
  localparam int DC_WAY_TB = 4;
  localparam int DC_CAPACITY_TB = 2 * 1024 * 8;
  localparam int BLK_SIZE_TB = 128;
  localparam int XLEN_TB = 32;

  // Clock and reset
  logic                           clk;
  logic                           rst_n;

  // DCache interfaces
  ceres_param::dcache_req_t       cache_req;
  ceres_param::dcache_res_t       cache_res;
  ceres_param::dlowX_req_t        lowX_req;
  ceres_param::dlowX_res_t        lowX_res;
  logic                           flush;
  logic                           fencei_stall;

  // Simple memory model
  logic                     [7:0] memory             [logic [31:0]];

  // Test statistics
  int                             load_count = 0;
  int                             store_count = 0;
  int                             mismatch_count = 0;
  int                             total_ops = 0;

  // DCache instance
  dcache #(
      .cache_req_t(ceres_param::dcache_req_t),
      .cache_res_t(ceres_param::dcache_res_t),
      .lowX_res_t (ceres_param::dlowX_res_t),
      .lowX_req_t (ceres_param::dlowX_req_t),
      .CACHE_SIZE (DC_CAPACITY_TB),
      .BLK_SIZE   (BLK_SIZE_TB),
      .XLEN       (XLEN_TB),
      .NUM_WAY    (DC_WAY_TB)
  ) dut (
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
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Memory model - responds to lowX requests
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      lowX_res.valid <= 1'b0;
      lowX_res.ready <= 1'b1;
      lowX_res.data  <= '0;
    end else begin
      // Default ready
      lowX_res.ready <= 1'b1;

      // Handle requests
      if (lowX_req.valid && lowX_res.ready) begin
        if (lowX_req.rw) begin
          // Write to memory
          for (int i = 0; i < 16; i++) begin
            memory[lowX_req.addr+i] = lowX_req.data[i*8+:8];
          end
          lowX_res.valid <= 1'b1;
          lowX_res.data  <= '0;
        end else begin
          // Read from memory
          for (int i = 0; i < 16; i++) begin
            lowX_res.data[i*8+:8] = memory[lowX_req.addr+i];
          end
          lowX_res.valid <= 1'b1;
        end
      end else begin
        lowX_res.valid <= 1'b0;
      end
    end
  end

  // Test sequence
  initial begin
    int    fd;
    string line;
    string op_type;
    logic [31:0] addr, expected_data, read_data;
    int op_count = 0;

    // Initialize
    rst_n = 0;
    flush = 0;
    cache_req = '0;

    repeat (10) @(posedge clk);
    rst_n = 1;
    repeat (5) @(posedge clk);

    // Open memory operations file
    fd = $fopen("/home/kerim/level-v/mem_ops.txt", "r");
    if (fd == 0) begin
      $display("ERROR: Cannot open mem_ops.txt");
      $finish;
    end

    $display("Starting dcache replay test...");

    // Process each operation
    while (!$feof(
        fd
    ) && op_count < 1000) begin  // Limit to first 1000 ops for quick test
      if ($fgets(line, fd)) begin
        if ($sscanf(line, "%s 0x%h 0x%h", op_type, addr, expected_data) == 3) begin
          op_count++;

          if (op_type == "load") begin
            // Perform load
            @(posedge clk);
            cache_req.valid <= 1'b1;
            cache_req.ready <= 1'b1;
            cache_req.addr <= addr;
            cache_req.rw <= 1'b0;  // Read
            cache_req.rw_size <= WORD;  // Word
            cache_req.uncached <= 1'b0;

            // Wait for response
            wait (cache_res.valid && cache_res.ready);
            read_data = cache_res.data;

            @(posedge clk);
            cache_req.valid <= 1'b0;

            // Check result
            if (read_data !== expected_data) begin
              $display("[MISMATCH] Load addr=0x%08x: expected=0x%08x got=0x%08x", addr, expected_data, read_data);
              mismatch_count++;
            end
            load_count++;

          end else if (op_type == "store") begin
            // Perform store
            @(posedge clk);
            cache_req.valid <= 1'b1;
            cache_req.ready <= 1'b1;
            cache_req.addr <= addr;
            cache_req.rw <= 1'b1;  // Write
            cache_req.rw_size <= WORD;  // Word
            cache_req.data <= expected_data;
            cache_req.uncached <= 1'b0;

            // Wait for response
            wait (cache_res.valid && cache_res.ready);

            @(posedge clk);
            cache_req.valid <= 1'b0;

            store_count++;
          end

          total_ops++;
        end
      end
    end

    $fclose(fd);

    // Report results
    $display("\n========== Test Results ==========");
    $display("Total operations: %0d", total_ops);
    $display("Loads:  %0d", load_count);
    $display("Stores: %0d", store_count);
    $display("Mismatches: %0d", mismatch_count);

    if (mismatch_count == 0) begin
      $display("✅ TEST PASSED - All operations match!");
    end else begin
      $display("❌ TEST FAILED - %0d mismatches found", mismatch_count);
    end

    $finish;
  end

  // Timeout
  initial begin
    #1000000;  // 1ms timeout
    $display("ERROR: Test timeout!");
    $finish;
  end

endmodule
