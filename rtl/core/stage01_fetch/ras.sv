/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/

`timescale 1ns / 1ps

module ras
  import ceres_param::*;
#(
    parameter RAS_SIZE = 64
) (
    input  logic            clk_i,
    input  logic            rst_ni,
    input  ras_t            restore_i,
    input  logic            req_valid_i,
    input  logic            j_type_i,
    input  logic            jr_type_i,
    input  logic [     4:0] rd_addr_i,
    input  logic [     4:0] r1_addr_i,
    input  logic [XLEN-1:0] return_addr_i,
    output ras_t            popped_o
);

  // RAS operation types
  typedef enum logic [1:0] {
    NONE,
    PUSH,
    POP,
    BOTH
  } ras_op_e;

  ras_t    ras     [RAS_SIZE-1:0];
  ras_op_e ras_op;
  logic    link_rd;
  logic    link_r1;

  always_comb begin
    ras_op  = NONE;
    link_rd = (rd_addr_i == 5'd1 || rd_addr_i == 5'd5);  // Link register x1 (ra) or x5 (t0)
    link_r1 = (r1_addr_i == 5'd1 || r1_addr_i == 5'd5);

    if (req_valid_i) begin
      if (j_type_i && link_rd) ras_op = PUSH;
      else if (jr_type_i && (link_rd || link_r1)) begin
        if (link_rd && link_r1) ras_op = (rd_addr_i == r1_addr_i) ? PUSH : BOTH;
        else if (link_r1) ras_op = POP;
        else ras_op = PUSH;
      end
    end
    popped_o.data  = ras[0].data;
    popped_o.valid = ras[0].valid && (req_valid_i && (ras_op inside {POP, BOTH}));
  end

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      ras <= '{default: 0};
    end else begin
      if (restore_i.valid) begin
        for (int i = RAS_SIZE - 1; i > 0; i--) begin
          ras[i].data  <= ras[i-1].data;
          ras[i].valid <= ras[i-1].valid;
        end
        ras[0].data  <= restore_i.data;
        ras[0].valid <= 1;  // pipeline bu gilgiiyi vermeki sanırım
      end else if (req_valid_i) begin
        case (ras_op)
          PUSH: begin
            for (int i = RAS_SIZE - 1; i > 0; i--) begin
              ras[i].data  <= ras[i-1].data;
              ras[i].valid <= ras[i-1].valid;
            end
            ras[0].data  <= return_addr_i;
            ras[0].valid <= 1'b1;
          end
          POP: begin
            for (int i = 0; i < RAS_SIZE - 1; i++) begin
              ras[i].data  <= ras[i+1].data;
              ras[i].valid <= ras[i+1].valid;
            end
            ras[RAS_SIZE-1].data  <= '0;
            ras[RAS_SIZE-1].valid <= 1'b0;
          end
          BOTH: begin
            ras[0].data  <= return_addr_i;
            ras[0].valid <= 1;
          end
        endcase
      end
    end
  end

endmodule
