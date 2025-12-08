`timescale 1ns / 1ps
// Top-level module with ports so Verilator C++ harness can drive/read them
module pma_tb (
    input  logic [31:0] tb_addr_i,
    output logic        tb_uncached_o,
    output logic        tb_memregion_o,
    output logic        tb_grand_o
);

  // Instantiate DUT and connect to top-level ports
  pma dut (
      .addr_i     (tb_addr_i),
      .uncached_o (tb_uncached_o),
      .memregion_o(tb_memregion_o),
      .grand_o    (tb_grand_o)
  );

endmodule
