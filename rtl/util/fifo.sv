/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
// Some design;
//    head = write pointer
//    tail = read pointer
module count_fifo #(  // counter
    parameter DATA_WIDTH = 8,
    parameter FIFO_DEPTH = 4
) (
    input logic clk,
    input logic rst,
    input logic write_en,
    input logic read_en,
    input logic [DATA_WIDTH-1:0] write_data,
    output logic [DATA_WIDTH-1:0] read_data,
    output logic full,
    output logic empty
);

  localparam ADDR_WIDTH = $clog2(FIFO_DEPTH);

  logic [DATA_WIDTH-1:0] fifo_mem[FIFO_DEPTH];
  logic [ADDR_WIDTH-1:0] write_ptr, read_ptr;
  logic [ADDR_WIDTH:0] fifo_count;

  always_ff @(posedge clk) begin
    if (rst) begin
      write_ptr  <= 0;
      read_ptr   <= 0;
      fifo_count <= 0;
    end else begin
      case ({
        write_en, read_en
      })
        2'b10:   fifo_count <= fifo_count + 1;
        2'b01:   fifo_count <= fifo_count - 1;
        default: fifo_count <= fifo_count;
      endcase
      if (write_en && !full) begin
        fifo_mem[write_ptr] <= write_data;
        write_ptr <= write_ptr + 1;
      end
      if (read_en && !empty) begin
        read_data <= fifo_mem[read_ptr];
        read_ptr  <= read_ptr + 1;
      end
    end
  end

  assign full  = (fifo_count == FIFO_DEPTH);
  assign empty = (fifo_count == 0);

endmodule

module le_fifo #(
    parameter DATA_WIDTH = 8,
    parameter FIFO_DEPTH = 4
) (
    input logic clk,
    input logic rst,
    input logic write_en,
    input logic read_en,
    input logic [DATA_WIDTH-1:0] write_data,
    output logic [DATA_WIDTH-1:0] read_data,
    output logic full,
    output logic empty
);

  localparam ADDR_WIDTH = $clog2(FIFO_DEPTH);
  logic [DATA_WIDTH-1:0] fifo_mem[FIFO_DEPTH];
  logic [ADDR_WIDTH-1:0] write_ptr, read_ptr;
  logic wrap_around;

  always_ff @(posedge clk) begin
    if (rst) begin
      write_ptr <= 0;
      read_ptr  <= 0;
    end else begin
      if (write_en && !full) begin
        fifo_mem[write_ptr] <= write_data;
        write_ptr <= write_ptr + 1;
      end
      if (read_en && !empty) begin
        read_data <= fifo_mem[read_ptr];
        read_ptr  <= read_ptr + 1;
      end
    end
  end

  assign full  = ((write_ptr + 1'b1) == read_ptr);
  assign empty = (write_ptr == read_ptr);

endmodule

module wbit_fifo #(
    parameter DATA_WIDTH = 8,
    parameter FIFO_DEPTH = 4
) (
    input logic clk,
    input logic rst,
    input logic write_en,
    input logic read_en,
    input logic [DATA_WIDTH-1:0] write_data,
    output logic [DATA_WIDTH-1:0] read_data,
    output logic full,
    output logic empty
);

  localparam ADDR_WIDTH = $clog2(FIFO_DEPTH);
  logic [DATA_WIDTH-1:0] fifo_mem[FIFO_DEPTH];
  logic [ADDR_WIDTH:0] write_ptr, read_ptr;
  logic wrap_around;

  always_ff @(posedge clk) begin
    if (rst) begin
      write_ptr <= 0;
      read_ptr  <= 0;
    end else begin
      if (write_en && !full) begin
        fifo_mem[write_ptr[ADDR_WIDTH-1:0]] <= write_data;
        write_ptr <= write_ptr + 1;
      end
      if (read_en && !empty) begin
        read_data <= fifo_mem[read_ptr[ADDR_WIDTH-1:0]];
        read_ptr  <= read_ptr + 1;
      end
    end
  end

  assign wrap_around = (write_ptr[ADDR_WIDTH] ^ read_ptr[ADDR_WIDTH]);

  assign full = wrap_around & (write_ptr[ADDR_WIDTH-1:0] == read_ptr[ADDR_WIDTH-1:0]);
  assign empty = (write_ptr == read_ptr);

endmodule
