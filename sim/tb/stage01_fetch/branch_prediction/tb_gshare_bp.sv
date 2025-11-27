`timescale 1ns / 1ps

module tb_gshare_bp;

  import ceres_param::*;

  logic                     clk;
  logic                     rst_ni;

  logic                     spec_hit_i;
  logic                     stall_i;
  logic                     is_comp_i;
  inst_t                    inst_i;
  logic          [XLEN-1:0] pc_target_i;
  logic          [XLEN-1:0] pc_i;
  logic          [XLEN-1:0] pc2_i;
  logic          [XLEN-1:0] pc4_i;
  logic                     fetch_valid_i;
  predict_info_t            spec_o;

  // Instantiate the DUT
  gshare_bp dut (
      .clk_i        (clk),
      .rst_ni       (rst_ni),
      .spec_hit_i   (spec_hit_i),
      .stall_i      (stall_i),
      .is_comp_i    (is_comp_i),
      .inst_i       (inst_i),
      .pc_target_i  (pc_target_i),
      .pc_i         (pc_i),
      .pc2_i        (pc2_i),
      .pc4_i        (pc4_i),
      .fetch_valid_i(fetch_valid_i),
      .spec_o       (spec_o)
  );

  // Clock generation
  always #5 clk = ~clk;

  // Helper task to simulate a branch
  task simulate_branch(input logic [XLEN-1:0] pc, input logic [XLEN-1:0] target, input logic predict_taken_expected);
    begin
      inst_i = '0;
      inst_i[6:0] = 7'b1100011;  // B-type opcode
      pc_i = pc;
      pc_target_i = target;
      pc2_i = pc + 2;
      pc4_i = pc + 4;
      is_comp_i = 0;
      fetch_valid_i = 1;
      spec_hit_i = 1;
      stall_i = 0;

      @(posedge clk);
      #1;

      if (spec_o.taken !== predict_taken_expected) $error("Prediction failed at pc=0x%0h. Expected taken=%0d, got=%0d", pc, predict_taken_expected, spec_o.taken);
      else $display("Prediction OK at pc=0x%0h -> taken: %0d", pc, spec_o.taken);

      fetch_valid_i = 0;
      @(posedge clk);
    end
  endtask

  // Test sequence
  initial begin
    clk = 0;
    rst_ni = 0;
    fetch_valid_i = 0;
    @(posedge clk);
    rst_ni = 1;
    @(posedge clk);

    // Test 1: Simulate not-taken branch (weakly not taken init)
    simulate_branch(32'h00001000, 32'h00002000, 0);

    // Test 2: Take same branch again (causing predictor to strengthen taken prediction)
    simulate_branch(32'h00001000, 32'h00002000, 0);
    simulate_branch(32'h00001000, 32'h00002000, 1);

    // Test 3: Another branch address
    simulate_branch(32'h00003000, 32'h00004000, 0);
    simulate_branch(32'h00003000, 32'h00004000, 1);

    $display("All tests completed.");
    $finish;
  end

endmodule
