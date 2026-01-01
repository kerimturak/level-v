/*
 * L2 Cache Testbench
 * Isolated test environment for L2 multibank non-blocking cache
 */
`timescale 1ns / 1ps

module l2_cache_tb
  import ceres_param::*;
();

  // ============================================================================
  // Parameters
  // ============================================================================
  localparam CLK_PERIOD = 10;  // 100 MHz
  localparam MEM_LATENCY = 5;  // Memory response latency in cycles

  // ============================================================================
  // DUT Signals
  // ============================================================================
  logic            clk;
  logic            rst_n;
  logic            flush;

  // L1 interface (2 ports: icache=0, dcache=1)
  lowX_req_t [1:0] l1_req;
  lowX_res_t [1:0] l1_res;

  // Memory request
  lowX_req_t       mem_req;
  lowX_res_t       mem_res;

  // ============================================================================
  // Test Control
  // ============================================================================
  integer          test_num;
  integer          pass_count;
  integer          fail_count;
  integer          log_file;
  string           test_name;

  // ============================================================================
  // Clock Generation
  // ============================================================================
  initial begin
    clk = 0;
    forever #(CLK_PERIOD / 2) clk = ~clk;
  end

  // ============================================================================
  // DUT Instantiation
  // ============================================================================
  l2_cache_multibank #(
      .CACHE_SIZE(16384),  // 16KB total (2 banks x 8KB)
      .NUM_BANKS (2)
  ) dut (
      .clk_i    (clk),
      .rst_ni   (rst_n),
      .flush_i  (flush),
      .l1_req_i (l1_req),
      .l1_res_o (l1_res),
      .mem_res_i(mem_res),
      .mem_req_o(mem_req)
  );

  // ============================================================================
  // Memory Model (Simple latency-based response)
  // ============================================================================
  typedef struct packed {
    logic valid;
    logic [31:0] addr;
    logic [3:0] id;
    int countdown;
  } mem_pending_t;

  mem_pending_t                mem_pending_q [$];
  logic         [BLK_SIZE-1:0] fake_mem_data;

  // Generate fake memory data based on address
  function automatic logic [BLK_SIZE-1:0] gen_mem_data(logic [31:0] addr);
    logic [BLK_SIZE-1:0] data;
    for (int i = 0; i < BLK_SIZE / 32; i++) begin
      data[i*32+:32] = addr + (i * 4);  // Sequential words
    end
    return data;
  endfunction

  // Memory response generation
  // mem_res.ready indicates memory can accept new requests
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      mem_res.valid <= 1'b0;
      mem_res.ready <= 1'b1;  // Memory always ready to accept
      mem_res.blk <= '0;
      mem_res.id <= '0;
    end else begin
      // Default: no response, but keep ready high
      mem_res.valid <= 1'b0;
      mem_res.ready <= 1'b1;  // Always ready to accept new requests

      // Accept new requests when ready
      if (mem_req.valid && mem_res.ready) begin
        mem_pending_t pending;
        pending.valid = 1'b1;
        pending.addr = mem_req.addr;
        pending.id = mem_req.id;
        pending.countdown = MEM_LATENCY;
        mem_pending_q.push_back(pending);
        $fdisplay(log_file, "[MEM] @%0t Accept req: addr=0x%08x id=%0d", $time, mem_req.addr, mem_req.id);
      end

      // Process pending requests
      for (int i = 0; i < mem_pending_q.size(); i++) begin
        if (mem_pending_q[i].countdown > 0) begin
          mem_pending_q[i].countdown--;
        end
      end

      // Send response for completed request
      if (mem_pending_q.size() > 0 && mem_pending_q[0].countdown == 0) begin
        mem_res.valid <= 1'b1;
        mem_res.blk <= gen_mem_data(mem_pending_q[0].addr);
        mem_res.id <= mem_pending_q[0].id;
        $fdisplay(log_file, "[MEM] @%0t Send response: addr=0x%08x id=%0d", $time, mem_pending_q[0].addr, mem_pending_q[0].id);
        mem_pending_q.pop_front();
      end
    end
  end

  // ============================================================================
  // Test Tasks
  // ============================================================================

  // Reset DUT
  task automatic reset_dut();
    $fdisplay(log_file, "\n[TB] Resetting DUT...");
    rst_n = 0;
    flush = 0;
    l1_req[0] = '0;
    l1_req[1] = '0;
    mem_pending_q.delete();
    repeat (5) @(posedge clk);
    rst_n = 1;
    repeat (2) @(posedge clk);
    $fdisplay(log_file, "[TB] Reset complete");
  endtask

  // Send L1 read request
  task automatic l1_read(input int port,  // 0=icache, 1=dcache
                         input logic [31:0] addr, input logic [3:0] id, output logic [BLK_SIZE-1:0] data, output logic success);
    int timeout_cnt;

    $fdisplay(log_file, "[TB] @%0t L1[%0d] READ request: addr=0x%08x id=%0d", $time, port, addr, id);

    // Wait for L2 ready
    timeout_cnt = 0;
    while (!l1_res[port].ready && timeout_cnt < 100) begin
      @(posedge clk);
      timeout_cnt++;
    end

    if (timeout_cnt >= 100) begin
      $fdisplay(log_file, "[TB] ERROR: Timeout waiting for L2 ready");
      success = 0;
      return;
    end

    // Send request
    l1_req[port].valid = 1'b1;
    l1_req[port].ready = 1'b1;  // L1 ready to receive response
    l1_req[port].addr = addr;
    l1_req[port].id = id;
    l1_req[port].rw = 1'b0;  // Read
    l1_req[port].uncached = 1'b0;
    l1_req[port].rw_size = NO_SIZE;
    l1_req[port].data = '0;

    @(posedge clk);

    // Deassert valid after one cycle (if accepted)
    if (l1_res[port].ready) begin
      $fdisplay(log_file, "[TB] @%0t L1[%0d] Request accepted", $time, port);
      l1_req[port].valid = 1'b0;
    end else begin
      // Keep valid until accepted
      timeout_cnt = 0;
      while (!l1_res[port].ready && timeout_cnt < 100) begin
        @(posedge clk);
        timeout_cnt++;
      end
      l1_req[port].valid = 1'b0;
    end

    // Wait for response
    timeout_cnt = 0;
    while (!l1_res[port].valid && timeout_cnt < 200) begin
      @(posedge clk);
      timeout_cnt++;
      // Log ready signal status
      if (timeout_cnt % 10 == 0) begin
        $fdisplay(log_file, "[TB] @%0t Waiting for response... ready=%0d valid=%0d", $time, l1_res[port].ready, l1_res[port].valid);
      end
    end

    if (timeout_cnt >= 200) begin
      $fdisplay(log_file, "[TB] ERROR: Timeout waiting for response");
      success = 0;
      return;
    end

    data = l1_res[port].blk;
    success = 1;
    $fdisplay(log_file, "[TB] @%0t L1[%0d] Got response: id=%0d data[31:0]=0x%08x", $time, port, l1_res[port].id, data[31:0]);
  endtask

  // Check test result
  task automatic check_result(input string name, input logic condition, input string msg);
    if (condition) begin
      $fdisplay(log_file, "[PASS] %s: %s", name, msg);
      pass_count++;
    end else begin
      $fdisplay(log_file, "[FAIL] %s: %s", name, msg);
      fail_count++;
    end
  endtask

  // ============================================================================
  // Test Cases
  // ============================================================================

  // Test 1: Simple read miss
  task automatic test_read_miss();
    logic [BLK_SIZE-1:0] data;
    logic                success;
    logic [        31:0] test_addr;

    test_name = "READ_MISS";
    $fdisplay(log_file, "\n========== TEST: %s ==========", test_name);

    reset_dut();

    // Read from cold cache - should miss
    test_addr = 32'h8000_0100;
    l1_read(0, test_addr, 4'd8, data, success);

    check_result(test_name, success, $sformatf("Read completed, data[31:0]=0x%08x", data[31:0]));
    check_result(test_name, data[31:0] == test_addr, $sformatf("Data correct (expected 0x%08x, got 0x%08x)", test_addr, data[31:0]));
  endtask

  // Test 2: Read hit (after miss fills cache)
  task automatic test_read_hit();
    logic [BLK_SIZE-1:0] data1, data2;
    logic success1, success2;
    logic [31:0] test_addr;
    int cycles_miss, cycles_hit;

    test_name = "READ_HIT";
    $fdisplay(log_file, "\n========== TEST: %s ==========", test_name);

    reset_dut();

    test_addr   = 32'h8000_0200;

    // First read - miss
    cycles_miss = $time;
    l1_read(0, test_addr, 4'd8, data1, success1);
    cycles_miss = ($time - cycles_miss) / CLK_PERIOD;

    // Second read - should hit
    cycles_hit  = $time;
    l1_read(0, test_addr, 4'd9, data2, success2);
    cycles_hit = ($time - cycles_hit) / CLK_PERIOD;

    check_result(test_name, success1 && success2, "Both reads completed");
    check_result(test_name, data1 == data2, "Data matches");
    check_result(test_name, cycles_hit < cycles_miss, $sformatf("Hit faster than miss (%0d vs %0d cycles)", cycles_hit, cycles_miss));
  endtask

  // Test 3: Concurrent requests from both ports
  task automatic test_concurrent_requests();
    logic [BLK_SIZE-1:0] data0, data1;
    logic success0, success1;
    logic [31:0] addr0, addr1;

    test_name = "CONCURRENT_REQ";
    $fdisplay(log_file, "\n========== TEST: %s ==========", test_name);

    reset_dut();

    // Different addresses to different banks
    addr0 = 32'h8000_0000;  // Bank 0 (bit 5 = 0)
    addr1 = 32'h8000_0020;  // Bank 1 (bit 5 = 1)

    // Send both requests simultaneously
    fork
      l1_read(0, addr0, 4'd8, data0, success0);
      l1_read(1, addr1, 4'd1, data1, success1);
    join

    check_result(test_name, success0, $sformatf("Port 0 read completed, data=0x%08x", data0[31:0]));
    check_result(test_name, success1, $sformatf("Port 1 read completed, data=0x%08x", data1[31:0]));
  endtask

  // Test 4: MSHR merge - same address from different ports
  task automatic test_mshr_merge();
    logic [BLK_SIZE-1:0] data0, data1;
    logic success0, success1;
    logic [31:0] test_addr;

    test_name = "MSHR_MERGE";
    $fdisplay(log_file, "\n========== TEST: %s ==========", test_name);

    reset_dut();

    // Same address from both ports
    test_addr = 32'h8000_0300;

    // Send both requests simultaneously
    fork
      l1_read(0, test_addr, 4'd8, data0, success0);
      l1_read(1, test_addr, 4'd1, data1, success1);
    join

    check_result(test_name, success0, "Port 0 completed");
    check_result(test_name, success1, "Port 1 completed");
    check_result(test_name, data0 == data1, "Both ports got same data");
  endtask

  // Test 5: Ready signal behavior - request not accepted when L2 busy
  task automatic test_ready_backpressure();
    int          ready_low_count;
    logic [31:0] addr;

    test_name = "READY_BACKPRESSURE";
    $fdisplay(log_file, "\n========== TEST: %s ==========", test_name);

    reset_dut();

    ready_low_count = 0;

    // Send multiple requests rapidly
    for (int i = 0; i < 8; i++) begin
      addr = 32'h8000_1000 + (i * 32'h100);  // Different cache lines

      l1_req[0].valid = 1'b1;
      l1_req[0].ready = 1'b1;
      l1_req[0].addr = addr;
      l1_req[0].id = 4'(8 + i);
      l1_req[0].rw = 1'b0;

      @(posedge clk);

      if (!l1_res[0].ready) begin
        ready_low_count++;
        $fdisplay(log_file, "[TB] Request %0d: L2 NOT ready (backpressure)", i);
        // Wait for ready
        while (!l1_res[0].ready) @(posedge clk);
      end

      l1_req[0].valid = 1'b0;
    end

    // Wait for all responses
    repeat (100) @(posedge clk);

    check_result(test_name, ready_low_count > 0, $sformatf("L2 applied backpressure %0d times", ready_low_count));
  endtask

  // ============================================================================
  // Main Test Sequence
  // ============================================================================
  initial begin
    // Open log file
    log_file = $fopen("l2_cache_tb.log", "w");
    if (log_file == 0) begin
      $display("ERROR: Cannot open log file");
      $finish;
    end

    $fdisplay(log_file, "========================================");
    $fdisplay(log_file, "L2 Cache Testbench");
    $fdisplay(log_file, "========================================");
    $fdisplay(log_file, "Start time: %0t", $time);

    test_num   = 0;
    pass_count = 0;
    fail_count = 0;

    // Run tests
    test_read_miss();
    test_read_hit();
    test_concurrent_requests();
    test_mshr_merge();
    test_ready_backpressure();

    // Summary
    $fdisplay(log_file, "\n========================================");
    $fdisplay(log_file, "TEST SUMMARY");
    $fdisplay(log_file, "========================================");
    $fdisplay(log_file, "PASSED: %0d", pass_count);
    $fdisplay(log_file, "FAILED: %0d", fail_count);
    $fdisplay(log_file, "========================================");

    if (fail_count == 0) begin
      $fdisplay(log_file, "ALL TESTS PASSED!");
      $display("ALL TESTS PASSED!");
    end else begin
      $fdisplay(log_file, "SOME TESTS FAILED!");
      $display("SOME TESTS FAILED! Check l2_cache_tb.log");
    end

    $fclose(log_file);
    $finish;
  end

  // Timeout watchdog
  initial begin
    #100000;
    $fdisplay(log_file, "\n[TB] TIMEOUT - Test did not complete in time");
    $fclose(log_file);
    $finish;
  end

endmodule
