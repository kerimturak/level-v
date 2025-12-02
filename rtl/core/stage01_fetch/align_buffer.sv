/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
/* verilator lint_off VARHIDDEN */
module align_buffer
  import ceres_param::*;
#(
    parameter CACHE_SIZE = ceres_param::ABUFF_SIZE,
    parameter BLK_SIZE   = ceres_param::BLK_SIZE,
    parameter XLEN       = ceres_param::XLEN,
    parameter NUM_WAY    = ceres_param::ABUFF_WAY
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
  // VERILATOR FIX: split_var directive helps Verilator optimize circular 
  // combinational logic in even/odd structs. Without this, Verilator's 2-state
  // simulation may evaluate signals in wrong order causing instruction corruption.
  // See: docs/verilator/bugs/002_combinational_loop_instruction_corruption.md
  bank_t even  /*verilator split_var*/, odd  /*verilator split_var*/;

  // VERILATOR FIX: These signals are part of circular dependency chain.
  // split_var helps break the UNOPTFLAT warning cycle.
  logic [               1:0] miss_state  /*verilator split_var*/;
  logic [               1:0] hit_state  /*verilator split_var*/;
  logic [     IDX_WIDTH-1:0] wr_idx;
  logic                      tag_wr_en;
  logic                      data_wr_en;
  logic [        TAG_SIZE:0] wr_tag;
  logic [   PARCEL_BITS-1:0] ebram                                                                                 [NUM_PARCELS/2-1:0] [NUM_SET-1:0];
  logic [   PARCEL_BITS-1:0] obram                                                                                 [NUM_PARCELS/2-1:0] [NUM_SET-1:0];
  logic [        TAG_SIZE:0] tag_ram                                                                               [      NUM_SET-1:0];
  // VERILATOR FIX: word_sel and half_sel are used in dynamic array indexing
  // which creates circular paths in Verilator's analysis.
  logic [WORD_SEL_WIDTH-1:0] word_sel  /*verilator split_var*/;
  logic                      half_sel  /*verilator split_var*/;
  logic                      overflow;  // Overflow flag when unaligned access causes index wrap-around
  logic                      unalign;  // Signal indicating an unaligned access (instruction spans two cache lines)
  logic [      TAG_SIZE-1:0] tag_plus1;

  // ============================================================================
  // Double Miss State Machine
  // ============================================================================
  // Problem: When unaligned access causes double miss (both cache lines miss),
  // we need TWO memory responses. But after first response arrives, the valid
  // signal would incorrectly trigger output before second response.
  //
  // Solution: 
  //   - ignore_valid_q: Masks the first response's valid for one cycle
  //   - waiting_second_q: Tracks that we're waiting for second cache line
  //   - masked_valid: The "real" valid signal that ignores first response glitch
  //
  // Timeline for double miss (unalign=1, miss_state=2'b11):
  //   Cycle N:   First request sent (odd bank's cache line)
  //   Cycle N+X: First response arrives (lowX_res_i.valid=1)
  //              → ignore_valid_q set to 1 (masks this valid)
  //              → waiting_second_q set to 1 (next cycle)
  //   Cycle N+X+1: ignore_valid_q=0, waiting_second_q=1
  //              → Second request sent (even bank's cache line)
  //   Cycle N+Y: Second response arrives
  //              → waiting_second_q && masked_valid → output valid!
  // ============================================================================
  logic                      masked_valid;
  logic                      ignore_valid_q;
  logic                      waiting_second_q;

  // waiting_second_q: Set after first response, cleared after second response
  always_ff @(posedge clk_i) begin
    if (!rst_ni | flush_i) begin
      waiting_second_q <= 1'b0;
    end else begin
      if ((miss_state == 2'b11) && masked_valid && unalign) begin
        // First response just processed, now wait for second
        waiting_second_q <= 1'b1;
      end else if (waiting_second_q && masked_valid) begin
        // Second response arrived, done waiting
        waiting_second_q <= 1'b0;
      end
    end
  end

  // ignore_valid_q: One-cycle pulse to mask the first response's valid
  // Uses lowX_res_i.valid (not masked_valid) to detect first response arrival
  always_ff @(posedge clk_i) begin
    if (!rst_ni | flush_i) begin
      ignore_valid_q <= 1'b0;
    end else begin
      if ((miss_state == 2'b11) && lowX_res_i.valid && unalign) begin
        // First response arrived, ignore it for one cycle
        ignore_valid_q <= 1'b1;
      end else begin
        // Clear after one cycle
        ignore_valid_q <= 1'b0;
      end
    end
  end

  // masked_valid: The effective valid signal, filtered for double miss
  assign masked_valid = lowX_res_i.valid && !ignore_valid_q;

  always_comb begin
    half_sel                = buff_req_i.addr[1];
    word_sel                = buff_req_i.addr[OFFSET_WIDTH-1:2];
    unalign                 = &{word_sel, half_sel};

    odd.rd_idx              = buff_req_i.addr[IDX_WIDTH+OFFSET_WIDTH-1:OFFSET_WIDTH];
    {overflow, even.rd_idx} = odd.rd_idx + {{(IDX_WIDTH - 1) {1'b0}}, unalign};

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

  for (genvar i = 0; i < NUM_WORDS; i++) begin : gen_parcel_logic
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

  // ============================================================================
  // Parcel Selection from Cache
  // ============================================================================
  // Memory layout for 128-bit cache line (4 words, 8 parcels):
  //   Word:    |  Word3  |  Word2  |  Word1  |  Word0  |
  //   Parcel:  | O3 | E3 | O2 | E2 | O1 | E1 | O0 | E0 |
  //   Addr:    | +E | +C | +A | +8 | +6 | +4 | +2 | +0 |
  //
  // Even bank (ebram): stores lower 16-bits of each word  (E0, E1, E2, E3)
  // Odd bank (obram):  stores upper 16-bits of each word  (O0, O1, O2, O3)
  // ============================================================================

  // Intermediate signals to break combinational loops for Verilator
  logic [ PARCEL_BITS-1:0] even_parcel_sel;
  logic [ PARCEL_BITS-1:0] odd_parcel_sel;
  logic [ PARCEL_BITS-1:0] even_deviceX_sel;
  logic [ PARCEL_BITS-1:0] odd_deviceX_sel;
  logic [WORD_SEL_WIDTH:0] parcel_idx;  // word_sel + half_sel

  always_comb begin : PARCEL_SELECT
    // Calculate parcel index (for even bank selection)
    parcel_idx = {1'b0, word_sel} + {2'b0, half_sel};

    // Even parcel selection - use case to avoid dynamic indexing issues
    if (unalign) begin
      even_parcel_sel = even.rd_parcel[0];
    end else begin
      case (parcel_idx[WORD_SEL_WIDTH-1:0])
        2'd0:    even_parcel_sel = even.rd_parcel[0];
        2'd1:    even_parcel_sel = even.rd_parcel[1];
        2'd2:    even_parcel_sel = even.rd_parcel[2];
        2'd3:    even_parcel_sel = even.rd_parcel[3];
        default: even_parcel_sel = even.rd_parcel[0];
      endcase
    end

    // Odd parcel selection - use case to avoid dynamic indexing issues
    case (word_sel)
      2'd0:    odd_parcel_sel = odd.rd_parcel[0];
      2'd1:    odd_parcel_sel = odd.rd_parcel[1];
      2'd2:    odd_parcel_sel = odd.rd_parcel[2];
      2'd3:    odd_parcel_sel = odd.rd_parcel[3];
      default: odd_parcel_sel = odd.rd_parcel[0];
    endcase

    // Assign to struct members
    even.parcel = even_parcel_sel;
    odd.parcel  = odd_parcel_sel;

    // Memory response parcels for miss cases
    // odd.deviceX_parcel:  upper 16-bit of selected word from memory response
    // even.deviceX_parcel: for unalign -> first parcel, else -> upper 16-bit of word
    case (word_sel)
      2'd0:    odd_deviceX_sel = lowX_res_i.blk[1*WORD_BITS-1-:PARCEL_BITS];
      2'd1:    odd_deviceX_sel = lowX_res_i.blk[2*WORD_BITS-1-:PARCEL_BITS];
      2'd2:    odd_deviceX_sel = lowX_res_i.blk[3*WORD_BITS-1-:PARCEL_BITS];
      2'd3:    odd_deviceX_sel = lowX_res_i.blk[4*WORD_BITS-1-:PARCEL_BITS];
      default: odd_deviceX_sel = lowX_res_i.blk[1*WORD_BITS-1-:PARCEL_BITS];
    endcase
    odd.deviceX_parcel = odd_deviceX_sel;

    if (unalign) begin
      even.deviceX_parcel = lowX_res_i.blk[PARCEL_BITS-1:0];
    end else begin
      even.deviceX_parcel = odd_deviceX_sel;  // Same as odd for non-unaligned
    end
  end

  // ============================================================================
  // Instruction Assembly (32-bit output)
  // ============================================================================
  // Case 1: half_sel=0 (word-aligned, addr[1]=0)
  //         Instruction spans: [addr: lower16] [addr+2: upper16]
  //         Output: {odd.parcel, even.parcel} = {upper16, lower16}
  //
  // Case 2: half_sel=1 (half-word offset, addr[1]=1)  
  //         Instruction spans: [addr: lower16] [addr+2: upper16 from next word]
  //         Output: {even.parcel, odd.parcel} = {next_word_lower16, current_word_upper16}
  //
  // Case 3: unalign=1 (cache line boundary crossing, addr=0x...E)
  //         Instruction spans two cache lines
  //         Output: {even.parcel(next_line), odd.parcel(current_line)}
  // ============================================================================
  always_comb begin : INST_ASSEMBLY
    // Default output
    buff_res_o.blk = {even.parcel, odd.parcel};

    if (waiting_second_q && masked_valid) begin
      // ----- DOUBLE MISS COMPLETION -----
      // Second response arrived for unaligned double miss:
      //   - odd.parcel: from buffer (first response already written)
      //   - even.deviceX_parcel: from current lowX response (second cache line)
      // Instruction: {upper16 from next line, lower16 from current line}
      buff_res_o.blk = {even.deviceX_parcel, odd.parcel};

    end else if (|miss_state && masked_valid) begin
      // ----- SINGLE MISS path: use data from memory response -----
      if (!half_sel && !unalign) begin
        // Word-aligned miss: extract full word directly from memory response
        buff_res_o.blk = lowX_res_i.blk[(word_sel*WORD_BITS)+:WORD_BITS];
      end else if (half_sel) begin
        // Half-word offset miss: combine parcels based on which bank missed
        case (miss_state)
          2'b01:   buff_res_o.blk = {even.deviceX_parcel, odd.parcel};  // Even miss only
          2'b10:   buff_res_o.blk = {even.parcel, odd.deviceX_parcel};  // Odd miss only  
          2'b11:   buff_res_o.blk = '0;  // Double miss (first response, don't output yet)
          default: buff_res_o.blk = {even.parcel, odd.parcel};
        endcase
      end
      // unalign case with miss is handled by double-miss logic above
    end else if (&hit_state) begin
      // ----- HIT path: use data from cache -----
      if (!half_sel) begin
        // Word-aligned hit: {upper16, lower16} = {odd, even}
        buff_res_o.blk = {odd.parcel, even.parcel};
      end else begin
        // Half-word offset hit: {next_lower16, current_upper16} = {even, odd}
        buff_res_o.blk = {even.parcel, odd.parcel};
      end
    end
    // else: default already set
  end

  // ============================================================================
  // Output Valid Signal Generation
  // ============================================================================
  // buff_res_o.valid indicates when a complete 32-bit instruction is ready.
  //
  // Valid conditions:
  //   1. DUAL HIT: Both banks hit → instruction ready immediately (same cycle)
  //      Condition: &hit_state
  //
  //   2. SINGLE MISS (word-aligned, half_sel=0): One memory response completes fetch
  //      Condition: |miss_state && !half_sel && masked_valid
  //
  //   3. SINGLE MISS (half-word, half_sel=1, one bank hit): Mixed hit/miss
  //      Condition: !(&miss_state) && half_sel && masked_valid
  //      Note: !(&miss_state) means NOT both missing → at least one hit
  //
  //   4. DOUBLE MISS (unalign): Both banks miss, instruction spans two cache lines
  //      Requires TWO memory responses. Second response completes the instruction.
  //      Condition: waiting_second_q && masked_valid
  // ============================================================================
  always_comb begin : OUTPUT_VALID_GEN
    // Local variables for readability
    logic single_response_sufficient;
    logic double_miss_complete;

    // Determine if single memory response is sufficient for valid output
    single_response_sufficient = (|miss_state && !half_sel) ||  // Word-aligned miss
    (!(&miss_state) && half_sel);  // Half-word with partial hit

    // Double miss completion: second response arrived, first line already in buffer
    double_miss_complete = waiting_second_q && masked_valid;

    buff_res_o.valid = &hit_state ||  // Case 1: Both banks hit
    (single_response_sufficient && masked_valid) ||  // Case 2,3: Single miss resolved
    double_miss_complete;  // Case 4: Double miss, second response

    buff_res_o.miss = |miss_state;
    buff_res_o.ready = 1;
    buff_res_o.waiting_second = waiting_second_q;  // Expose to fetch for handshake control

    // ========================================================================
    // Lower Level Request Generation (lowX_req_o)
    // ========================================================================
    // Controls when to send cache line fetch requests to memory/lower cache.
    //
    // Key insight: 
    //   - unalign=0: Both parcels are in SAME cache line → single request
    //   - unalign=1: Parcels span TWO cache lines → may need two requests
    //   - uncached: Non-cacheable access (MMIO), bypass buffer entirely
    // ========================================================================
    lowX_req_o.valid = 1'b0;
    lowX_req_o.uncached = buff_req_i.uncached;

    // Request valid generation
    if (waiting_second_q && !masked_valid) begin
      // ---- DOUBLE MISS: Second request ----
      // First response received, now fetch the second cache line (even bank)
      lowX_req_o.valid = !buff_req_i.uncached;

    end else if (&miss_state) begin
      // ---- BOTH BANKS MISS ----
      if (masked_valid) begin
        // Response just arrived - don't send new request this cycle
        // (for double miss, waiting_second_q handles next cycle)
        lowX_req_o.valid = 1'b0;
      end else begin
        // Initial request: fetch first (or only) cache line
        // If unalign=0: single line contains both parcels
        // If unalign=1: this fetches odd bank's line first
        lowX_req_o.valid = !buff_req_i.uncached;
      end

    end else if (|miss_state) begin
      // ---- SINGLE BANK MISS ----
      // One bank hit, one miss - need single fetch
      lowX_req_o.valid = !buff_req_i.uncached && !masked_valid && !waiting_second_q;

    end else begin
      // ---- BOTH BANKS HIT ----
      // No fetch needed
      lowX_req_o.valid = 1'b0;
    end

    lowX_req_o.ready = rst_ni && !flush_i;

    // ========================================================================
    // Address Calculation for Lower Level Request
    // ========================================================================
    // Cache line aligned address (clear low bits for block alignment)
    //
    // Address cases:
    //   unalign=0: Always fetch base_addr (both parcels in same line)
    //   unalign=1, even miss only (3'b101): Fetch next block (even bank's line)
    //   unalign=1, double miss (3'b111): 
    //     - First request: base_addr (odd bank's line)
    //     - Second request: base_addr + BLOCK_BYTES (even bank's line)
    // ========================================================================
    begin
      localparam int BLOCK_BYTES = BLK_SIZE / 8;  // 128 bits = 16 bytes
      logic [XLEN-1:0] base_addr;
      base_addr = buff_req_i.addr & ~(BLOCK_BYTES - 1);

      if (waiting_second_q) begin
        // Double miss second request: fetch even bank's cache line
        lowX_req_o.addr = base_addr + BLOCK_BYTES;
      end else begin
        case ({
          unalign, odd.miss, even.miss
        })
          3'b101:  lowX_req_o.addr = base_addr + BLOCK_BYTES;  // Even miss only, unaligned
          3'b111:  lowX_req_o.addr = base_addr;  // Double miss: odd line first
          default: lowX_req_o.addr = base_addr;  // Same line (incl. 3'b011)
        endcase
      end
    end

  end

endmodule
