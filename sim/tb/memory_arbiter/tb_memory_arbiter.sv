`timescale 1ns / 1ps

// Self-checking testbench for memory_arbiter
module tb_memory_arbiter;
  import ceres_param::*;

  // Clock / reset
  logic clk = 0;
  always #5 clk = ~clk;
  logic       rst_ni = 0;

  // Interface signals (types from ceres_param)
  ilowX_req_t    icache_req_i;
  dlowX_req_t    dcache_req_i;
  ilowX_res_t    icache_res_o;
  dlowX_res_t    dcache_res_o;
  lowX_res_t     mem_bus_res_i;
  lowX_req_t     mem_bus_req_o;

  // DUT
  memory_arbiter dut (
      .clk_i         (clk),
      .rst_ni        (rst_ni),
      .icache_req_i  (icache_req_i),
      .dcache_req_i  (dcache_req_i),
      .icache_res_o  (icache_res_o),
      .dcache_res_o  (dcache_res_o),
      .mem_bus_res_i (mem_bus_res_i),
      .mem_bus_req_o (mem_bus_req_o)
  );

  // Simple memory model for mem_bus: when mem_bus_req_o.valid, respond after 2 cycles
  logic [31:0] captured_addr;
  always_ff @(posedge clk) begin
    if (!rst_ni) begin
      mem_bus_res_i.valid <= 1'b0;
      mem_bus_res_i.data <= '0;
      captured_addr <= '0;
    end else begin
      // Capture requests
      if (mem_bus_req_o.valid) captured_addr <= mem_bus_req_o.addr;

      // Produce a response two cycles later
      mem_bus_res_i.valid <= 1'b0;
      if ($rose(mem_bus_req_o.valid)) begin
        // schedule a response: assert next cycle and provide data
        mem_bus_res_i.valid <= 1'b1;
        mem_bus_res_i.data  <= BLK_SIZE'(captured_addr);
      end
    end
  end

  // Helper tasks
  task send_icache_req(input logic [31:0] addr);
    begin
      icache_req_i = '{default: 0};
      icache_req_i.valid = 1'b1;
      icache_req_i.addr = addr;
      @(posedge clk);
      icache_req_i.valid = 1'b0;
    end
  endtask

  task send_dcache_req(input logic [31:0] addr, input logic [31:0] data);
    begin
      dcache_req_i = '{default: 0};
      dcache_req_i.valid = 1'b1;
      dcache_req_i.addr = addr;
      dcache_req_i.data = BLK_SIZE'(data);
      @(posedge clk);
      dcache_req_i.valid = 1'b0;
    end
  endtask

  // Simple checker state
  int errors = 0;
  int checks = 0;

  // Monitor mem_bus_req_o and validate source selection
  always @(posedge clk) begin
    if (!rst_ni);
    else begin
      if (mem_bus_req_o.valid) begin
        checks++;
        // If icache_reg is valid (latched), expect icache to be forwarded unless round-robin selected DCACHE
        // We simply check that addr matches one of the issuers
        if (mem_bus_req_o.addr !== icache_req_i.addr && mem_bus_req_o.addr !== dcache_req_i.addr) begin
          $display("[ERROR] mem_bus forwarded addr 0x%08h doesn't match any issuer @ %0t", mem_bus_req_o.addr, $time);
          errors++;
        end else begin
          $display("[INFO] mem_bus forwarded addr 0x%08h (icache=0x%08h, dcache=0x%08h) @ %0t", mem_bus_req_o.addr, icache_req_i.addr, dcache_req_i.addr, $time);
        end
      end
    end
  end

  // Test sequence
  initial begin
    // Init
    rst_ni = 1'b0;
    icache_req_i = '{default: 0};
    dcache_req_i = '{default: 0};
    mem_bus_res_i = '{default: 0};

    repeat (5) @(posedge clk);
    rst_ni = 1'b1;
    repeat (3) @(posedge clk);

    $display("\n=== MEMORY ARBITER SELF-CHECK START ===\n");

    // Test 1: ICACHE only
    send_icache_req(32'h1000);
    repeat (4) @(posedge clk);

    // Test 2: DCACHE only
    send_dcache_req(32'h2000, 32'hA5A5A5A5);
    repeat (4) @(posedge clk);

    // Test 3: Both requests simultaneously
    icache_req_i = '{default: 0};
    dcache_req_i = '{default: 0};
    icache_req_i.valid = 1'b1;
    icache_req_i.addr = 32'h3000;
    dcache_req_i.valid = 1'b1;
    dcache_req_i.addr = 32'h4000;
    dcache_req_i.data = BLK_SIZE'(32'hDEADBEEF);
    @(posedge clk);
    icache_req_i.valid = 1'b0;
    dcache_req_i.valid = 1'b0;
    repeat (8) @(posedge clk);

    // Summary
    $display("\n=== SUMMARY: checks=%0d errors=%0d ===", checks, errors);
    if (errors == 0) $display("*** MEMORY ARBITER SELF-CHECK PASSED ***");
    else $display("*** MEMORY ARBITER SELF-CHECK FAILED (%0d errors) ***", errors);

    $finish;
  end

endmodule
