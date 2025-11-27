`timescale 1ns / 1ps

module tb_ras;
  // Clock and reset signals
  logic        clk;
  logic        rst_ni;

  // Signals going to the RAS module
  logic        restore_i;
  logic [31:0] restore_pc_i;
  logic        req_valid_i;
  logic        j_type_i;
  logic        jr_type_i;
  logic [ 4:0] rd_addr_i;
  logic [ 4:0] r1_addr_i;
  logic [31:0] return_addr_i;

  // Signals coming from the RAS module
  logic [31:0] popped_addr_o;
  logic        predict_valid_o;

  // UUT (Unit Under Test) instantiation
  ras uut (
      .clk_i          (clk),
      .rst_ni         (rst_ni),
      .restore_i      (restore_i),
      .restore_pc_i   (restore_pc_i),
      .req_valid_i    (req_valid_i),
      .j_type_i       (j_type_i),
      .jr_type_i      (jr_type_i),
      .rd_addr_i      (rd_addr_i),
      .r1_addr_i      (r1_addr_i),
      .return_addr_i  (return_addr_i),
      .popped_addr_o  (popped_addr_o),
      .predict_valid_o(predict_valid_o)
  );

  // Clock generation: 10 ns period
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Stimulus and self-checking test scenarios
  initial begin
    // Initial values
    rst_ni        <= 0;
    restore_i     <= 0;
    restore_pc_i  <= 32'd0;
    req_valid_i   <= 0;
    j_type_i      <= 0;
    jr_type_i     <= 0;
    rd_addr_i     <= 5'd0;
    r1_addr_i     <= 5'd0;
    return_addr_i <= 32'd0;

    // Apply reset
    repeat (2) @(posedge clk);
    rst_ni <= 1;
    repeat (2) @(posedge clk);

    // ------------------------------------------------------
    // Test 1: PUSH Operation (j_type_i=1 and link register = 1)
    // ------------------------------------------------------
    rd_addr_i     <= 5'd1;  // link register: 1 or 5
    r1_addr_i     <= 5'd0;
    j_type_i      <= 1;
    jr_type_i     <= 0;
    req_valid_i   <= 1;
    return_addr_i <= 32'hA000_0000;  // Address to be pushed
    @(posedge clk);
    req_valid_i <= 0;
    j_type_i    <= 0;
    #1;
    // During PUSH, predict_valid_o should be inactive
    if (predict_valid_o !== 0) $error("Test 1 Failed: predict_valid_o should be 0 during PUSH.");

    // ------------------------------------------------------
    // Test 2: POP Operation (jr_type_i=1 and link register = 1)
    // ------------------------------------------------------
    // Assume that the previously pushed address is on the stack
    @(posedge clk);
    rd_addr_i   <= 5'd0;  // rd not used
    r1_addr_i   <= 5'd1;  // link register: 1 or 5
    j_type_i    <= 0;
    jr_type_i   <= 1;
    req_valid_i <= 1;
    @(posedge clk);
    req_valid_i <= 0;
    jr_type_i   <= 0;
    @(posedge clk);

    // ------------------------------------------------------
    // Test 3: BOTH Operation (jr_type_i=1 with both rd and r1 link registers active)
    // ------------------------------------------------------
    rd_addr_i     <= 5'd1;  // link
    r1_addr_i     <= 5'd5;  // link
    jr_type_i     <= 1;
    req_valid_i   <= 1;
    return_addr_i <= 32'hB000_0000;  // New address

    #1;
    // During POP, the popped address should be the one pushed before (0xA000_0000)
    if (popped_addr_o !== 32'hA000_0000) $error("Test 2 Failed: Expected popped address 0xA0000000, got: %h", popped_addr_o);

    if (predict_valid_o !== 1) $error("Test 2 Failed: predict_valid_o should be 1 during POP.");
    @(posedge clk);
    req_valid_i <= 0;
    jr_type_i   <= 0;
    @(posedge clk);
    #1;
    // BOTH operation: both pop and push happen, updating the top of the stack
    if (popped_addr_o !== 32'hB000_0000) $error("Test 3 Failed: Expected top address after BOTH to be 0xB0000000, got: %h", popped_addr_o);

    if (predict_valid_o !== 1) $error("Test 3 Failed: predict_valid_o should be 1 during BOTH.");

    // ------------------------------------------------------
    // Test 4: RESTORE Operation (restore_i=1)
    // ------------------------------------------------------
    restore_i    <= 1;
    restore_pc_i <= 32'hC000_0000; // Restore address
    @(posedge clk);
    restore_i <= 0;
    @(posedge clk);
    #1;
    // During RESTORE, the top of the stack should be updated to restore_pc_i
    if (popped_addr_o !== 32'hC000_0000) $error("Test 4 Failed: Expected restored address 0xC0000000, got: %h", popped_addr_o);

    $display("All tests passed successfully.");
    repeat (5) @(posedge clk);
    $finish;
  end

endmodule
