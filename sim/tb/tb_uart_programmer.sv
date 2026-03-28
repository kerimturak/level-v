// tb_uart_programmer — Verilator-only harness for UART → wrapper_ram programming verification.
// C++ drives clk/reset, bit-banged prog UART, and normal-port RAM reads.
`timescale 1ns / 1ps

module tb_uart_programmer (
    input wire clk_i,
    input wire rst_ni,

    input  wire         ram_prog_rx_i,
    output wire         prog_mode_led_o,
    output wire         system_reset_o,

    input  wire  [11:0] addr_i,
    input  wire [127:0] wdata_i,
    input  wire  [15:0] wstrb_i,
    output wire [127:0] rdata_o,
    input  wire         rd_en_i
);

  wrapper_ram #(
      .RAM_DEPTH(4096)
  ) dut (
      .clk_i         (clk_i),
      .rst_ni        (rst_ni),
      .addr_i        (addr_i),
      .wdata_i       (wdata_i),
      .wstrb_i       (wstrb_i),
      .rdata_o       (rdata_o),
      .rd_en_i       (rd_en_i),
      .ram_prog_rx_i (ram_prog_rx_i),
      .system_reset_o(system_reset_o),
      .prog_mode_led_o(prog_mode_led_o)
  );

endmodule
