`timescale 1ns / 1ps

import level_param::*;


module tb_align_buffer;

  // Clock, reset, and flush signals
  logic       clk;
  logic       rst_n;
  logic       flush;

  // Input/output signals for the DUT
  abuff_req_t buff_req;
  abuff_res_t buff_res;
  blowX_res_t lowX_res;
  blowX_req_t lowX_req;

  // DUT instance
  align_buffer #(
      .CACHE_SIZE(256),  // Example value; must match BUFFER_CAPACITY
      .BLK_SIZE  (128),
      .XLEN      (32),
      .NUM_WAY   (1),
      .DATA_WIDTH(16)
  ) dut (
      .clk_i     (clk),
      .rst_ni    (rst_n),
      .flush_i   (flush),
      .buff_req_i(buff_req),
      .buff_res_o(buff_res),
      .lowX_res_i(lowX_res),
      .lowX_req_o(lowX_req)
  );

  // Clock generation: 10 ns period
  always #5 clk = ~clk;

  // Helper signal to supply LowX response one cycle late
  // This block makes lowX_res active on the next clock cycle
  // depending on buff_req.valid.
  logic lowX_response_pending;
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) lowX_response_pending <= 0;
    else
      // Produce response on the next cycle, not in the same cycle as buff_req.valid
      lowX_response_pending <= buff_req.valid;
  end

  // Drive lowX_res: if lowX_response_pending is active,
  // different data blocks are supplied according to buff_req.addr.
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      lowX_res <= '{valid: 0, ready: 0, blk: 128'h0};
    end else begin
      if (lowX_response_pending) begin
        // Example: respond based on different address values.
        if (buff_req.addr == 32'h0000_0010) begin
          lowX_res <= '{valid: 1, ready: 0, blk: 128'hAAAA_BBBB_CCCC_DDDD_EEEE_FFFF_1111_2222};
        end else if (buff_req.addr == 32'h0000_00F8) begin
          lowX_res <= '{valid: 1, ready: 0, blk: 128'hDEAD_BEEF_DEAD_BEEF_DEAD_BEEF_DEAD_BEEF};
        end else if (buff_req.uncached) begin
          lowX_res <= '{valid: 0, ready: 0, blk: 128'h0};  // No response in uncached cases
        end else begin
          lowX_res <= '{valid: 1, ready: 0, blk: 128'h1234_5678_9ABC_DEF0_1234_5678_9ABC_DEF0};
        end
      end else begin
        lowX_res <= '{valid: 0, ready: 0, blk: 128'h0};
      end
    end
  end

  // Stimulus generation
  initial begin
    // Initial values
    clk      = 0;
    rst_n    = 0;
    flush    = 0;
    buff_req = '{valid: 0, ready: 1, uncached: 0, addr: 32'h0};

    // Apply reset
    #20;
    rst_n = 1;
    #10;

    // Scenario 1: Aligned access
    // When the address aligns to cache line boundaries:
    // BOFFSET = $clog2(128/8)=4, so addr[3:0] = 4'b0000
    buff_req = '{valid: 1, ready: 1, uncached: 0, addr: 32'h0000_0010};
    #10;  // buff_req valid; lowX_res will be produced on the next cycle.
    #20;
    buff_req.valid = 0;
    #20;

    // Scenario 2: Unaligned access
    // Unaligned case: addr[BOFFSET-1:1] all ones (e.g. BOFFSET=4, addr[3:1]=3'b111)
    buff_req = '{valid: 1, ready: 1, uncached: 0, addr: 32'h0000_00F8};
    #10;
    #20;
    buff_req.valid = 0;
    #20;

    // Scenario 3: Uncached access (lowX_res delayed / not provided)
    buff_req = '{valid: 1, ready: 1, uncached: 1, addr: 32'h0000_0100};
    #10;
    #20;
    buff_req.valid = 0;
    #20;

    // Scenario 4: Flush asserted
    flush = 1;
    #10;
    flush = 0;
    #20;

    // Finish
    #50;
    $stop;
  end

  // Monitoring (optional)
  initial begin
    $display("Time\tclk\trst_n\tflush\tbuff_req.addr\tbuff_req.valid\tbuff_res.blk\tbuff_res.valid\tbuff_res.miss");
    $monitor("%0t\t%b\t%b\t%b\t%h\t%b\t%h\t%b\t%b", $time, clk, rst_n, flush, buff_req.addr, buff_req.valid, buff_res.blk, buff_res.valid, buff_res.miss);
  end

endmodule
