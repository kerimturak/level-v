`timescale 1ns / 1ps
/*
 * VGA framebuffer read master → Wishbone classic read.
 * RAM_SIZE_KB: physical RAM window [0x8000_0000 .. 0x8000_0000+N). Fetches at/above
 * that top ack with 0 (black in 1bpp) so a 40 KiB FPGA can still run 640×480 timing
 * without illegal Wishbone or overlapping the bitstream heap.
 */
import level_param::*;

module vga_fb_wishbone #(
    parameter int unsigned RAM_SIZE_KB = 40
) (
    input logic clk_i,
    input logic rst_ni,

    input logic fb_req_i,
    input logic [31:0] fb_addr_i,
    output logic [31:0] fb_data_o,
    output logic fb_ack_o,

    output wb_master_t wb_m_o,
    input wb_slave_t wb_s_i
);

  localparam logic [31:0] RAM_BASE     = 32'h8000_0000;
  localparam logic [31:0] RAM_LAST_EX  = RAM_BASE + (RAM_SIZE_KB * 1024);  // first byte *past* RAM

  typedef enum logic [1:0] {
    ST_IDLE,
    ST_BUSY,
    ST_OOB
  } state_e;

  state_e st;
  logic [31:0] adr_q;

  wire addr_oob = (fb_addr_i >= RAM_LAST_EX);

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      st    <= ST_IDLE;
      adr_q <= 32'h0;
    end else begin
      unique case (st)
        ST_IDLE: begin
          if (fb_req_i) begin
            if (addr_oob) st <= ST_OOB;
            else begin
              adr_q <= {fb_addr_i[31:2], 2'b00};
              st    <= ST_BUSY;
            end
          end
        end
        ST_BUSY: begin
          if (wb_s_i.ack || wb_s_i.err) st <= ST_IDLE;
        end
        ST_OOB: st <= ST_IDLE;
        default: st <= ST_IDLE;
      endcase
    end
  end

  assign wb_m_o.adr = adr_q;
  assign wb_m_o.dat = 32'h0;
  assign wb_m_o.sel = 4'hF;
  assign wb_m_o.we  = 1'b0;
  assign wb_m_o.cti = WB_CTI_CLASSIC;
  assign wb_m_o.bte = WB_BTE_LINEAR;
  assign wb_m_o.cyc = (st == ST_BUSY);
  assign wb_m_o.stb = (st == ST_BUSY);

  assign fb_ack_o  = ((st == ST_BUSY) && (wb_s_i.ack || wb_s_i.err)) || (st == ST_OOB);
  assign fb_data_o = (st == ST_OOB) ? 32'h0 : (wb_s_i.err ? 32'h0 : wb_s_i.dat);

endmodule
