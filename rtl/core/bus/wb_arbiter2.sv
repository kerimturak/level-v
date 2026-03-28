`timescale 1ns / 1ps
/*
 * Wishbone B4 priority arbiter: port 0 (CPU) wins when .cyc is asserted.
 * Port 1 (VGA framebuffer) is stalled while the CPU holds an outstanding
 * transaction. Suitable for read-only secondary master with rare contention.
 */
import level_param::*;

module wb_arbiter2 (
    input wb_master_t wb_m_cpu_i,
    output wb_slave_t wb_s_cpu_o,

    input wb_master_t wb_m_vga_i,
    output wb_slave_t wb_s_vga_o,

    output wb_master_t wb_m_o,
    input wb_slave_t wb_s_i
);

  // CPU holds the bus whenever it asserts an active cycle (classic WB in-flight).
  wire grant_cpu = wb_m_cpu_i.cyc;

  always_comb begin
    wb_m_o = grant_cpu ? wb_m_cpu_i : wb_m_vga_i;
  end

  assign wb_s_cpu_o.dat = wb_s_i.dat;
  assign wb_s_cpu_o.ack = wb_s_i.ack && grant_cpu;
  assign wb_s_cpu_o.err = wb_s_i.err && grant_cpu;
  assign wb_s_cpu_o.rty = wb_s_i.rty && grant_cpu;
  assign wb_s_cpu_o.stall = wb_s_i.stall | (wb_m_vga_i.cyc & wb_m_vga_i.stb & ~grant_cpu);

  assign wb_s_vga_o.dat = wb_s_i.dat;
  assign wb_s_vga_o.ack = wb_s_i.ack & ~grant_cpu;
  assign wb_s_vga_o.err = wb_s_i.err & ~grant_cpu;
  assign wb_s_vga_o.rty = wb_s_i.rty & ~grant_cpu;
  assign wb_s_vga_o.stall = wb_s_i.stall | (wb_m_cpu_i.cyc & wb_m_cpu_i.stb & grant_cpu);

endmodule
