`timescale 1ns / 1ps
`include "level_defines.svh"

module memory
  import level_param::*;
(
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  stall_e                stall_i,
    input  logic                  fe_flush_cache_i,
    input  dlowX_res_t            lx_dres_i,
    output dlowX_req_t            lx_dreq_o,
    output logic       [XLEN-1:0] me_data_o,
    output logic                  dmiss_stall_o,
    output logic                  fencei_stall_o,
    input  data_req_t             me_data_req_i,
    input  data_req_t             ex_data_req_i
);

  dcache_req_t            dcache_req;
  dcache_res_t            dcache_res;
  logic        [XLEN-1:0] rd_data;
  logic                   uncached;

  // -------------------------------------------------------------------
  // Request change detection (same as before — breaks comb loops)
  // -------------------------------------------------------------------
  logic                   ex_valid_q;
  logic        [XLEN-1:0] ex_addr_q;
  logic                   ex_rw_q;
  logic        [     1:0] ex_rw_size_q;

  logic pipe2_advanced_q;
  always_ff @(posedge clk_i) begin
    if (!rst_ni)
      pipe2_advanced_q <= 1'b0;
    else
      pipe2_advanced_q <= !(stall_i inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL});
  end

  always_ff @(posedge clk_i) begin
    if (!rst_ni || fe_flush_cache_i) begin
      ex_valid_q   <= 1'b0;
      ex_addr_q    <= '0;
      ex_rw_q      <= 1'b0;
      ex_rw_size_q <= NO_SIZE;
    end else begin
      ex_valid_q   <= ex_data_req_i.valid;
      ex_addr_q    <= ex_data_req_i.addr;
      ex_rw_q      <= ex_data_req_i.rw;
      ex_rw_size_q <= ex_data_req_i.rw_size;
    end
  end

  logic req_changed;
  assign req_changed = (ex_data_req_i.addr != ex_addr_q) ||
                       (ex_data_req_i.rw   != ex_rw_q)   ||
                       (ex_data_req_i.rw_size != ex_rw_size_q) ||
                       (ex_data_req_i.valid && !ex_valid_q);

  logic new_req;
  assign new_req = ex_data_req_i.valid && req_changed && pipe2_advanced_q;

  // Store buffer status (forward declare for vlog before store_pending ff)
  logic sb_full;
  logic sb_empty;

  // -------------------------------------------------------------------
  // Store / load classification
  // -------------------------------------------------------------------
  logic is_store;
  logic is_load;
  assign is_store = ex_data_req_i.valid && ex_data_req_i.rw;
  assign is_load  = ex_data_req_i.valid && !ex_data_req_i.rw;

  logic store_fire;
  logic cached_store_fire;
  logic uncached_store_fire;
  assign store_fire           = is_store && new_req;
  assign cached_store_fire    = store_fire && !uncached;
  assign uncached_store_fire  = store_fire && uncached;

  // Sustain stall when store buffer is full until room becomes available.
  // pipe2 is frozen during the stall so ex_data_req_i stays valid.
  logic store_pending;
  always_ff @(posedge clk_i) begin
    if (!rst_ni || fe_flush_cache_i)
      store_pending <= 1'b0;
    else if (cached_store_fire && sb_full)
      store_pending <= 1'b1;
    else if (store_pending && !sb_full)
      store_pending <= 1'b0;
  end

  logic store_buffer_write;
  assign store_buffer_write = (cached_store_fire && !sb_full) ||
                              (store_pending && !sb_full);

  // -------------------------------------------------------------------
  // Store buffer instance
  // -------------------------------------------------------------------
  logic            sb_fwd_hit, sb_fwd_conflict;
  logic [XLEN-1:0] sb_fwd_data;
  logic            sb_drain_valid, sb_drain_uncached;
  logic [XLEN-1:0] sb_drain_addr, sb_drain_data;
  rw_size_e        sb_drain_size;
  logic            sb_drain_ack;

  store_buffer i_store_buffer (
      .clk_i          (clk_i),
      .rst_ni         (rst_ni),
      .wr_valid_i     (store_buffer_write),
      .wr_addr_i      (ex_data_req_i.addr),
      .wr_data_i      (ex_data_req_i.data),
      .wr_size_i      (ex_data_req_i.rw_size),
      .wr_uncached_i  (1'b0),
      .fwd_addr_i     (ex_data_req_i.addr),
      .fwd_size_i     (ex_data_req_i.rw_size),
      .fwd_hit_o      (sb_fwd_hit),
      .fwd_data_o     (sb_fwd_data),
      .fwd_conflict_o (sb_fwd_conflict),
      .drain_valid_o  (sb_drain_valid),
      .drain_addr_o   (sb_drain_addr),
      .drain_data_o   (sb_drain_data),
      .drain_size_o   (sb_drain_size),
      .drain_uncached_o(sb_drain_uncached),
      .drain_ack_i    (sb_drain_ack),
      .full_o         (sb_full),
      .empty_o        (sb_empty)
  );

  // -------------------------------------------------------------------
  // Dcache transaction tracking
  // -------------------------------------------------------------------
  logic load_active;
  logic drain_active;
  logic uc_store_active;
  logic load_pending;
  logic uc_drain_pending;

  logic dcache_busy;
  assign dcache_busy = load_active || drain_active || uc_store_active;

  // A load that couldn't be forwarded or fired (conflict / dcache busy)
  // stays pending until it resolves via forwarding or dcache read.
  logic load_fwd_resolve;
  assign load_fwd_resolve = load_pending && is_load && sb_fwd_hit && !sb_fwd_conflict;

  logic load_req_fire;
  assign load_req_fire = ((is_load && new_req) || load_pending) &&
                         !sb_fwd_hit && !sb_fwd_conflict &&
                         !dcache_busy && !uc_drain_pending;

  // Drain fires when dcache is idle and buffer has entries.
  // Allowed during load_pending — draining resolves conflicts.
  logic drain_fire;
  assign drain_fire = sb_drain_valid && !dcache_busy && !load_req_fire
                      && !uncached_store_fire;

  // Uncached store handling: drain buffer first, then send directly
  logic [XLEN-1:0] uc_addr_q, uc_data_q;
  rw_size_e        uc_size_q;

  logic uc_store_fire;
  assign uc_store_fire = (uncached_store_fire && sb_empty && !dcache_busy) ||
                         (uc_drain_pending && sb_empty && !dcache_busy);

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      uc_drain_pending <= 1'b0;
    end else begin
      if (uncached_store_fire && !sb_empty) begin
        uc_drain_pending <= 1'b1;
        uc_addr_q <= ex_data_req_i.addr;
        uc_data_q <= ex_data_req_i.data;
        uc_size_q <= ex_data_req_i.rw_size;
      end else if (uc_drain_pending && sb_empty) begin
        uc_drain_pending <= 1'b0;
      end
    end
  end

  // Track pending load: set when a load can't fire (conflict / busy),
  // clear when it fires to dcache or resolves via forwarding.
  always_ff @(posedge clk_i) begin
    if (!rst_ni || fe_flush_cache_i) begin
      load_pending <= 1'b0;
    end else begin
      if (is_load && new_req && !sb_fwd_hit &&
          (sb_fwd_conflict || dcache_busy || uc_drain_pending))
        load_pending <= 1'b1;
      else if (load_req_fire || load_fwd_resolve)
        load_pending <= 1'b0;
      else if (!is_load && pipe2_advanced_q)
        load_pending <= 1'b0;
    end
  end

  // Store-buffer drain ack: dcache can complete a buffered store in the same cycle as
  // `drain_fire` (e.g. cache hit). `drain_active` is registered the cycle after `drain_fire`,
  // so requiring `drain_active && dcache_res.valid` misses that cycle and never pops SB.
  assign sb_drain_ack = dcache_res.valid && (drain_active || drain_fire);

  // Transaction state tracking
  always_ff @(posedge clk_i) begin
    if (!rst_ni || fe_flush_cache_i) begin
      load_active     <= 1'b0;
      drain_active    <= 1'b0;
      uc_store_active <= 1'b0;
    end else begin
      if (dcache_res.valid) begin
        load_active     <= 1'b0;
        uc_store_active <= 1'b0;
      end
      if (load_req_fire) load_active <= 1'b1;
      if (uc_store_fire) uc_store_active <= 1'b1;

      if (sb_drain_ack) drain_active <= 1'b0;
      else if (drain_fire) drain_active <= 1'b1;
    end
  end

  // -------------------------------------------------------------------
  // Dcache request mux (load > uncached store > drain)
  // -------------------------------------------------------------------
  always_comb begin
    if (load_req_fire) begin
      dcache_req.valid    = 1'b1;
      dcache_req.addr     = ex_data_req_i.addr;
      dcache_req.ready    = 1'b1;
      dcache_req.rw       = 1'b0;
      dcache_req.rw_size  = ex_data_req_i.rw_size;
      dcache_req.data     = '0;
      dcache_req.uncached = uncached;
    end else if (uc_store_fire) begin
      dcache_req.valid    = 1'b1;
      dcache_req.addr     = uc_drain_pending ? uc_addr_q : ex_data_req_i.addr;
      dcache_req.ready    = 1'b1;
      dcache_req.rw       = 1'b1;
      dcache_req.rw_size  = uc_drain_pending ? uc_size_q : ex_data_req_i.rw_size;
      dcache_req.data     = uc_drain_pending ? uc_data_q : ex_data_req_i.data;
      dcache_req.uncached = 1'b1;
    end else if (drain_fire) begin
      dcache_req.valid    = 1'b1;
      dcache_req.addr     = sb_drain_addr;
      dcache_req.ready    = 1'b1;
      dcache_req.rw       = 1'b1;
      dcache_req.rw_size  = sb_drain_size;
      dcache_req.data     = sb_drain_data;
      dcache_req.uncached = sb_drain_uncached;
    end else begin
      dcache_req.valid    = 1'b0;
      dcache_req.addr     = ex_data_req_i.addr;
      dcache_req.ready    = 1'b1;
      dcache_req.rw       = 1'b0;
      dcache_req.rw_size  = ex_data_req_i.rw_size;
      dcache_req.data     = '0;
      dcache_req.uncached = uncached;
    end
  end

  // -------------------------------------------------------------------
  // Stall generation
  // -------------------------------------------------------------------
  // Fence.i: drain store buffer before flushing dcache
  logic fencei_pending;
  logic dcache_fencei_stall;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      fencei_pending <= 1'b0;
    end else begin
      if (fe_flush_cache_i && !sb_empty)
        fencei_pending <= 1'b1;
      else if (fencei_pending && sb_empty)
        fencei_pending <= 1'b0;
    end
  end

  logic dcache_flush;
  assign dcache_flush = (fe_flush_cache_i && sb_empty) ||
                        (fencei_pending && sb_empty);

  // Load blocked on first cycle (conflict / dcache busy) — combinational
  logic first_cycle_load_blocked;
  assign first_cycle_load_blocked = is_load && new_req && !sb_fwd_hit &&
                                    (sb_fwd_conflict || dcache_busy || uc_drain_pending);

  // Pending load stalls unless resolved by forwarding this cycle
  logic load_stall_pending;
  assign load_stall_pending = load_pending && !load_fwd_resolve;

  always_comb begin
    dmiss_stall_o = load_req_fire
                  || (load_active && !dcache_res.valid)
                  || first_cycle_load_blocked
                  || load_stall_pending
                  || (cached_store_fire && sb_full)
                  || store_pending
                  || uncached_store_fire
                  || uc_drain_pending
                  || (uc_store_active && !dcache_res.valid)
                  || fencei_pending;
  end

  assign fencei_stall_o = dcache_fencei_stall || fencei_pending ||
                         (fe_flush_cache_i && !sb_empty);

  // -------------------------------------------------------------------
  // PMA
  // -------------------------------------------------------------------
  pma i_dpma (
      .addr_i     (ex_data_req_i.addr),
      .uncached_o (uncached),
      .memregion_o(),
      .grand_o    ()
  );

  // -------------------------------------------------------------------
  // D-cache
  // -------------------------------------------------------------------
  dcache #(
      .cache_req_t(dcache_req_t),
      .cache_res_t(dcache_res_t),
      .lowX_req_t (dlowX_req_t),
      .lowX_res_t (dlowX_res_t),
      .CACHE_SIZE (DC_CAPACITY),
      .BLK_SIZE   (BLK_SIZE),
      .XLEN       (XLEN),
      .NUM_WAY    (DC_WAY)
  ) i_dcache (
      .clk_i         (clk_i),
      .rst_ni        (rst_ni),
      .flush_i       (dcache_flush),
      .cache_req_i   (dcache_req),
      .cache_res_o   (dcache_res),
      .lowX_res_i    (lx_dres_i),
      .lowX_req_o    (lx_dreq_o),
      .fencei_stall_o(dcache_fencei_stall)
  );

`ifdef LOG_CACHE
  cache_logger i_cache_logger (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .cache_req_i(dcache_req),
      .cache_res_i(dcache_res)
  );
`endif

  // -------------------------------------------------------------------
  // Read data: forwarded from store buffer OR from dcache
  // -------------------------------------------------------------------
  logic [ 7:0] selected_byte;
  logic [15:0] selected_halfword;

  always_comb begin : read_data_size_handler
    rd_data = (is_load && sb_fwd_hit && !sb_fwd_conflict) ? sb_fwd_data : dcache_res.data;
    me_data_o = '0;

    selected_byte     = rd_data[(ex_data_req_i.addr[1:0]*8)+:8];
    selected_halfword = rd_data[(ex_data_req_i.addr[1]*16)+:16];

    unique case (ex_data_req_i.rw_size)
      BYTE:    me_data_o = ex_data_req_i.ld_op_sign ? {{24{selected_byte[7]}}, selected_byte} : {24'b0, selected_byte};
      HALF:    me_data_o = ex_data_req_i.ld_op_sign ? {{16{selected_halfword[15]}}, selected_halfword} : {16'b0, selected_halfword};
      WORD:    me_data_o = rd_data;
      default: me_data_o = '0;
    endcase
  end

endmodule
