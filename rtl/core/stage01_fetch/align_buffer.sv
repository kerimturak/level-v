/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
module align_buffer
  import ceres_param::*;
#(
    parameter CACHE_SIZE = 512,
    parameter BLK_SIZE   = 128,
    parameter XLEN       = 32,
    parameter NUM_WAY    = 1
) (
    input  logic       clk_i,
    input  logic       rst_ni,
    input  logic       flush_i,
    input  abuff_req_t buff_req_i,
    output abuff_res_t buff_res_o,
    input  blowX_res_t lowX_res_i,
    output blowX_req_t lowX_req_o
);

  localparam NUM_SET = (CACHE_SIZE / (BLK_SIZE * NUM_WAY));  // All in bits
  localparam IDX_WIDTH = $clog2(NUM_SET);
  localparam OFFSET_WIDTH = $clog2(BLK_SIZE / 8);
  localparam TAG_SIZE = XLEN - IDX_WIDTH - OFFSET_WIDTH;

  localparam int WORD_BITS = 32;
  localparam int NUM_WORDS = BLK_SIZE / WORD_BITS;
  localparam int WORD_SEL_WIDTH = $clog2(BLK_SIZE / 32);

  localparam int PARCEL_BITS = 16;  // typically 16
  localparam int PARCELS_PER_WORD = WORD_BITS / PARCEL_BITS;
  localparam int NUM_PARCELS = NUM_WORDS * PARCELS_PER_WORD;

  typedef struct packed {
    logic                                      valid;
    logic                                      match;
    logic                                      miss;
    logic                                      hit;
    logic [IDX_WIDTH-1:0]                      rd_idx;
    logic [IDX_WIDTH-1:0]                      data_wr_idx;
    logic                                      tag_wr_en;
    logic [NUM_PARCELS/2-1:0][PARCEL_BITS-1:0] wr_parcel;
    logic [NUM_PARCELS/2-1:0][PARCEL_BITS-1:0] rd_parcel;
    logic [TAG_SIZE:0]                         rd_tag;
    logic [TAG_SIZE:0]                         wr_tag;
    logic [PARCEL_BITS-1:0]                    parcel;
    logic [PARCEL_BITS-1:0]                    deviceX_parcel;
  } bank_t;
  bank_t even, odd;

  logic [               1:0] miss_state;
  logic [               1:0] hit_state;
  logic [     IDX_WIDTH-1:0] wr_idx;
  logic                      tag_wr_en;
  logic                      data_wr_en;
  logic [        TAG_SIZE:0] wr_tag;
  logic [   PARCEL_BITS-1:0] ebram                                                                                 [NUM_PARCELS/2-1:0] [NUM_SET-1:0];
  logic [   PARCEL_BITS-1:0] obram                                                                                 [NUM_PARCELS/2-1:0] [NUM_SET-1:0];
  logic [        TAG_SIZE:0] tag_ram                                                                               [      NUM_SET-1:0];
  logic [WORD_SEL_WIDTH-1:0] word_sel;
  logic                      half_sel;
  logic                      overflow;  // Overflow flag when unaligned access causes index wrap-around
  logic                      unalign;  // Signal indicating an unaligned access (instruction spans two cache lines)
  logic [      TAG_SIZE-1:0] tag_plus1;

  // Fix for lingering valid signal during double miss
  logic                      masked_valid;
  logic                      ignore_valid_q;
  logic                      waiting_second_q;

  always_ff @(posedge clk_i) begin
    if (!rst_ni | flush_i) begin
      waiting_second_q <= 1'b0;
    end else begin
      if ((miss_state == 2'b11) && masked_valid && unalign) begin
        waiting_second_q <= 1'b1;
      end else if (waiting_second_q && masked_valid) begin
        waiting_second_q <= 1'b0;
      end
    end
  end

  always_ff @(posedge clk_i) begin
    if (!rst_ni | flush_i) begin
      ignore_valid_q <= 1'b0;
    end else begin
      if ((miss_state == 2'b11) && lowX_res_i.valid && unalign) begin
        ignore_valid_q <= 1'b1;
      end else begin
        ignore_valid_q <= 1'b0;
      end
    end
  end

  assign masked_valid = lowX_res_i.valid && !ignore_valid_q;

  always_comb begin
    half_sel                = buff_req_i.addr[1];
    word_sel                = buff_req_i.addr[OFFSET_WIDTH-1:2];
    unalign                 = &{word_sel, half_sel};

    odd.rd_idx              = buff_req_i.addr[IDX_WIDTH+OFFSET_WIDTH-1:OFFSET_WIDTH];
    {overflow, even.rd_idx} = odd.rd_idx + unalign;

    odd.wr_tag              = {1'b1, buff_req_i.addr[XLEN-1 : IDX_WIDTH+OFFSET_WIDTH]};
    tag_plus1               = buff_req_i.addr[XLEN-1 : IDX_WIDTH+OFFSET_WIDTH] + 1;
    even.wr_tag             = overflow ? {1'b1, tag_plus1} : odd.wr_tag;

    even.rd_tag             = tag_ram[even.rd_idx];
    odd.rd_tag              = tag_ram[odd.rd_idx];
    even.valid              = even.rd_tag[TAG_SIZE];
    odd.valid               = odd.rd_tag[TAG_SIZE];

    even.match              = (even.rd_tag[TAG_SIZE-1:0] == even.wr_tag[TAG_SIZE-1:0]);
    odd.match               = (odd.rd_tag[TAG_SIZE-1:0] == odd.wr_tag[TAG_SIZE-1:0]);

    even.miss               = buff_req_i.valid && !(even.valid && even.match);
    even.hit                = buff_req_i.valid && (even.valid && even.match);
    odd.miss                = buff_req_i.valid && !(odd.valid && odd.match);
    odd.hit                 = buff_req_i.valid && (odd.valid && odd.match);

    miss_state              = {odd.miss, even.miss};
    hit_state               = {odd.hit, even.hit};

    wr_tag                  = odd.miss ? odd.wr_tag : even.wr_tag;
    wr_idx                  = odd.miss ? odd.rd_idx : even.rd_idx;

    even.tag_wr_en          = masked_valid && !buff_req_i.uncached && !odd.miss && even.miss;
    odd.tag_wr_en           = masked_valid && !buff_req_i.uncached && odd.miss;
    tag_wr_en               = masked_valid && !buff_req_i.uncached && (odd.miss || (!odd.miss && even.miss));

    even.data_wr_idx        = odd.tag_wr_en ? odd.rd_idx : even.rd_idx;
    odd.data_wr_idx         = even.tag_wr_en && !odd.tag_wr_en ? even.rd_idx : odd.rd_idx;

    data_wr_en              = even.tag_wr_en || odd.tag_wr_en;
  end

  for (genvar i = 0; i < NUM_WORDS; i++) begin
    always_comb begin
      even.wr_parcel[i] = lowX_res_i.blk[i*WORD_BITS+:PARCEL_BITS];
      odd.wr_parcel[i]  = lowX_res_i.blk[(2*i+1)*PARCEL_BITS+:PARCEL_BITS];
      even.rd_parcel[i] = ebram[i][even.rd_idx];
      odd.rd_parcel[i]  = obram[i][odd.rd_idx];
    end

    always_ff @(posedge clk_i) begin
      if (data_wr_en) ebram[i][even.data_wr_idx] <= even.wr_parcel[i];
      if (data_wr_en) obram[i][odd.data_wr_idx] <= odd.wr_parcel[i];
    end
  end

  always_ff @(posedge clk_i) begin
    if (!rst_ni | flush_i) begin
      tag_ram <= '{default: '0};
    end else begin
      // For now, iterate over one way (future expansion to set-associative caches is planned).
      for (int i = 0; i < 1; i = i + 1) begin
        if (tag_wr_en) begin
          // Write the computed tag into the tag RAM at the selected index.
          tag_ram[wr_idx][i*(TAG_SIZE+1)+:(TAG_SIZE+1)] <= wr_tag[i*(TAG_SIZE+1)+:TAG_SIZE+1];
        end
      end
    end
  end

  always_comb begin
    even.parcel = unalign ? even.rd_parcel[0] : even.rd_parcel[word_sel+half_sel];
    odd.parcel = odd.rd_parcel[word_sel];
    odd.deviceX_parcel = lowX_res_i.blk[((word_sel+1)*WORD_BITS)-1-:PARCEL_BITS];
    even.deviceX_parcel = unalign ? lowX_res_i.blk[PARCEL_BITS-1 : 0] : lowX_res_i.blk[((word_sel+1)*WORD_BITS)-1-:PARCEL_BITS];
  end

  always_comb begin : EVEN_ODD_COMBINE
    if (!unalign && !half_sel && |miss_state && masked_valid) begin
      buff_res_o.blk = lowX_res_i.blk[((word_sel+1)*WORD_BITS)-1-:WORD_BITS];
    end else if (half_sel && |miss_state && masked_valid) begin
      case (miss_state)
        2'b00: buff_res_o.blk = {even.parcel, odd.parcel};  // Should never occur if both are hit.
        2'b01: buff_res_o.blk = {even.deviceX_parcel, odd.parcel};  // Lower (even) miss; use deviceX parcel.
        2'b10: buff_res_o.blk = {even.parcel, odd.deviceX_parcel};  // Upper (odd) miss; use deviceX parcel.
        2'b11: buff_res_o.blk = '0;  // Both paths miss.
      endcase
    end else if (!half_sel && &hit_state) begin
      buff_res_o.blk = {odd.parcel, even.parcel};
    end else begin
      buff_res_o.blk = {even.parcel, odd.parcel};
    end
  end

  // Combinational block to generate final valid/ready signals and prepare the lower-level request.
  always_comb begin
    buff_res_o.valid    = (&hit_state || (((|miss_state && !(half_sel)) || (!(&miss_state) && (half_sel))) && masked_valid));
    buff_res_o.miss     = |miss_state;
    buff_res_o.ready    = 1;

    lowX_req_o.valid    = 1'b0;
    lowX_req_o.uncached = buff_req_i.uncached;

    // Generate the lower level request signal.
    if (&miss_state) begin
      // When both even and odd paths miss:
      if (masked_valid) begin
        lowX_req_o.valid = (unalign ? !buff_req_i.uncached : 0);
      end else begin
        lowX_req_o.valid = !buff_req_i.uncached;
      end
    end else if (|miss_state) begin
      lowX_req_o.valid = !buff_req_i.uncached && !masked_valid && !waiting_second_q;
    end else begin
      lowX_req_o.valid = 0;
    end
    lowX_req_o.ready = rst_ni && !flush_i;

    // Compute block-aligned address for lower-level fetch requests.  The
    // previous implementation used `('1 << (NUM_WORDS))` which is a single
    // bit, not a mask; that caused incorrect lower-level addresses and
    // parcel mixing across blocks. Use a proper mask that clears the
    // low-order byte offset bits (BLK_SIZE/8 bytes per block).
    begin
      localparam int BLOCK_BYTES = BLK_SIZE / 8;
      logic [XLEN-1:0] base_addr;
      base_addr = buff_req_i.addr & ~(BLOCK_BYTES - 1);
      case ({
        unalign, odd.miss, even.miss
      })
        3'b101:  lowX_req_o.addr = base_addr + BLOCK_BYTES;
        // When both cache lines miss (3'b111) and unalign is set:
        // - Before first response: fetch odd cache line (base_addr)
        // - After first response (masked_valid): fetch even cache line (base_addr + BLOCK_BYTES)
        3'b111:  lowX_req_o.addr = masked_valid ? (base_addr + BLOCK_BYTES) : base_addr;
        default: lowX_req_o.addr = base_addr;
      endcase
    end

  end

`ifdef ALIGN_LOGGER
  // Disable with +define+ALIGN_LOGGER (default off)
  initial begin
    $display("[align_buffer] LowX response monitor initialized at time %0t", $time);
  end

  always @(posedge clk_i) begin
    if (lowX_res_i.valid) begin
      $display("[%0t] lowX_res_i.valid=1 | blk = %h", $time, lowX_res_i.blk);
    end
  end
`endif

endmodule
