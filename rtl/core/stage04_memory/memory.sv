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

  // Dual-port dcache interface
  dcache_req_t            ld_dcache_req;
  dcache_res_t            ld_dcache_res;
  dcache_req_t            st_dcache_req;
  dcache_res_t            st_dcache_res;
  logic        [XLEN-1:0] rd_data;
  logic                   uncached;

  // -------------------------------------------------------------------
  // Request change detection (same as before — breaks comb loops)
  // -------------------------------------------------------------------
  logic                   ex_valid_q;
  logic        [XLEN-1:0] ex_addr_q;
  logic                   ex_rw_q;
  logic        [     1:0] ex_rw_size_q;

  logic                   pipe2_advanced_q;
  always_ff @(posedge clk_i) begin
    if (!rst_ni) pipe2_advanced_q <= 1'b0;
    else pipe2_advanced_q <= !(stall_i inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL});
  end

  always_ff @(posedge clk_i) begin
    if (!rst_ni || fe_flush_cache_i) begin
      ex_valid_q   <= 1'b0;
      // ex_addr_q/ex_rw_q/ex_rw_size_q: no reset — overwritten every cycle
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
  assign req_changed = (ex_data_req_i.addr != ex_addr_q) || (ex_data_req_i.rw != ex_rw_q) || (ex_data_req_i.rw_size != ex_rw_size_q) || (ex_data_req_i.valid && !ex_valid_q);

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
  assign store_fire          = is_store && new_req;
  assign cached_store_fire   = store_fire && !uncached;
  assign uncached_store_fire = store_fire && uncached;

  // Sustain stall when store buffer is full until room becomes available.
  // pipe2 is frozen during the stall so ex_data_req_i stays valid.
  logic store_pending;
  always_ff @(posedge clk_i) begin
    if (!rst_ni || fe_flush_cache_i) store_pending <= 1'b0;
    else if (cached_store_fire && sb_full) store_pending <= 1'b1;
    else if (store_pending && !sb_full) store_pending <= 1'b0;
  end

  logic store_buffer_write;
  assign store_buffer_write = (cached_store_fire && !sb_full) || (store_pending && !sb_full);

  // -------------------------------------------------------------------
  // Store buffer instance
  // -------------------------------------------------------------------
  logic sb_fwd_hit, sb_fwd_conflict;
  logic [XLEN-1:0] sb_fwd_data;
  logic            sb_fwd_partial;
  logic [XLEN-1:0] sb_fwd_partial_data;
  logic [     3:0] sb_fwd_byte_mask;
  logic sb_drain_valid, sb_drain_uncached;
  logic [XLEN-1:0] sb_drain_addr, sb_drain_data;
  rw_size_e sb_drain_size;
  logic     sb_drain_ack;

  store_buffer i_store_buffer (
      .clk_i             (clk_i),
      .rst_ni            (rst_ni),
      .wr_valid_i        (store_buffer_write),
      .wr_addr_i         (ex_data_req_i.addr),
      .wr_data_i         (ex_data_req_i.data),
      .wr_size_i         (ex_data_req_i.rw_size),
      .wr_uncached_i     (1'b0),
      .fwd_addr_i        (ex_data_req_i.addr),
      .fwd_size_i        (ex_data_req_i.rw_size),
      .fwd_hit_o         (sb_fwd_hit),
      .fwd_data_o        (sb_fwd_data),
      .fwd_conflict_o    (sb_fwd_conflict),
      .fwd_partial_o     (sb_fwd_partial),
      .fwd_partial_data_o(sb_fwd_partial_data),
      .fwd_byte_mask_o   (sb_fwd_byte_mask),
      .drain_valid_o     (sb_drain_valid),
      .drain_addr_o      (sb_drain_addr),
      .drain_data_o      (sb_drain_data),
      .drain_size_o      (sb_drain_size),
      .drain_uncached_o  (sb_drain_uncached),
      .drain_ack_i       (sb_drain_ack),
      .full_o            (sb_full),
      .empty_o           (sb_empty)
  );

  // -------------------------------------------------------------------
  // Dcache transaction tracking (dual-port: LD + ST independent)
  // -------------------------------------------------------------------
  logic load_active;
  logic drain_active;
  logic uc_store_active;
  logic load_pending;
  logic uc_drain_pending;
  // Prefetch / next-line (Questa vlog: declare before first assign/use)
  logic pf_active;
  logic pf_fire;

  // No serialization — load and store ports are independent
  logic ld_port_busy;
  assign ld_port_busy = load_active || pf_active;

  // A load that couldn't be forwarded or fired (conflict / ld_port busy)
  // stays pending until it resolves via forwarding or dcache read.
  logic load_fwd_resolve;
  assign load_fwd_resolve = load_pending && is_load && sb_fwd_hit && !sb_fwd_conflict;

  // Partial forwarding: load fires to dcache, on response merge SB bytes
  logic load_partial_q;

  logic load_req_fire;
  assign load_req_fire = ((is_load && new_req) || load_pending) && !sb_fwd_hit && !sb_fwd_conflict && !ld_port_busy && !uc_drain_pending;

  // Drain fires when store port is ready and buffer has entries.
  // Fire-and-forget: drain ack on store port accept, even on miss.
  logic st_port_busy;
  assign st_port_busy = drain_active || uc_store_active;

  logic drain_fire;
  assign drain_fire = sb_drain_valid && !st_port_busy && !uncached_store_fire && st_dcache_res.ready;

  // Uncached store handling: drain buffer first, then send directly
  logic [XLEN-1:0] uc_addr_q, uc_data_q;
  rw_size_e uc_size_q;

  logic     uc_store_fire;
  assign uc_store_fire = ((uncached_store_fire && sb_empty && !st_port_busy) || (uc_drain_pending && sb_empty && !st_port_busy)) && st_dcache_res.ready;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      uc_drain_pending <= 1'b0;
    end else begin
      if (uncached_store_fire && !uc_store_fire) begin
        // UC store requested but couldn't fire (SB not empty / port busy / dcache not ready)
        uc_drain_pending <= 1'b1;
        uc_addr_q <= ex_data_req_i.addr;
        uc_data_q <= ex_data_req_i.data;
        uc_size_q <= ex_data_req_i.rw_size;
      end else if (uc_store_fire) begin
        uc_drain_pending <= 1'b0;
      end
    end
  end

  // Track pending load: set when a load can't fire (conflict / busy),
  // clear when it fires to dcache or resolves via forwarding.
  always_ff @(posedge clk_i) begin
    if (!rst_ni || fe_flush_cache_i) begin
      load_pending   <= 1'b0;
      load_partial_q <= 1'b0;
    end else begin
      if (is_load && new_req && !sb_fwd_hit && (sb_fwd_conflict || ld_port_busy || uc_drain_pending)) load_pending <= 1'b1;
      else if (load_req_fire || load_fwd_resolve) load_pending <= 1'b0;
      else if (!is_load && pipe2_advanced_q) load_pending <= 1'b0;

      // Track partial forwarding state — capture on fire OR when blocked
      // so the SB data is preserved even if entries drain while port is busy.
      if ((load_req_fire || first_cycle_load_blocked) && sb_fwd_partial) load_partial_q <= 1'b1;
      else if (ld_dcache_res.valid && load_active) load_partial_q <= 1'b0;
      else if (fe_flush_cache_i) load_partial_q <= 1'b0;
    end
  end

  // Fire-and-forget: drain ack when store port accepts the request.
  // Miss handling is dcache's responsibility via MSHR — SB pops immediately.
  assign sb_drain_ack = drain_fire || (drain_active && st_dcache_res.valid);

  // Transaction state tracking (pf_active declared above)

  always_ff @(posedge clk_i) begin
    if (!rst_ni || fe_flush_cache_i) begin
      load_active     <= 1'b0;
      drain_active    <= 1'b0;
      uc_store_active <= 1'b0;
      pf_active       <= 1'b0;
    end else begin
      // Load port: ld_dcache_res
      if (ld_dcache_res.valid) begin
        load_active <= 1'b0;
        pf_active   <= 1'b0;
      end
      if (load_req_fire) begin
        load_active <= 1'b1;
        pf_active   <= 1'b0;
      end else if (pf_fire) begin
        pf_active <= 1'b1;
      end

      // Store port: st_dcache_res
      if (st_dcache_res.valid) uc_store_active <= 1'b0;
      if (uc_store_fire) uc_store_active <= 1'b1;

      // Drain: fire-and-forget, ack pops SB immediately
      if (sb_drain_ack) drain_active <= 1'b0;
      else if (drain_fire) drain_active <= 1'b1;
    end
  end

  // -------------------------------------------------------------------
  // Next-line prefetcher (on D-cache miss → fetch next cache line)
  // -------------------------------------------------------------------
  localparam int NLP_LINE_BYTES = BLK_SIZE / 8;  // 16 bytes
  localparam int NLP_LINE_OFF = $clog2(NLP_LINE_BYTES);  // 4 bits

  logic        pf_valid;
  logic [31:0] pf_addr;
  logic        pf_ready;

  // Miss detection: one cycle after load_req_fire, if load_active is
  // still high (no immediate hit), it is a cache miss.
  logic        load_fired_q;
  always_ff @(posedge clk_i) begin
    if (!rst_ni) load_fired_q <= 1'b0;
    else load_fired_q <= load_req_fire;
  end

  logic miss_detected;
  assign miss_detected = load_fired_q && load_active && !ld_dcache_res.valid;

  // Latch the miss address so we can compute next-line target
  logic [31:0] miss_addr_q;
  always_ff @(posedge clk_i) begin
    // No reset — only used after load_req_fire writes it
    if (load_req_fire) miss_addr_q <= ex_data_req_i.addr;
  end

  // Next-line target: line-align miss addr, then +1 line
  logic [31:0] nl_target;
  assign nl_target = {miss_addr_q[31:NLP_LINE_OFF] + 1'b1, {NLP_LINE_OFF{1'b0}}};

  // Don't prefetch into uncached / peripheral region (only RAM >= 0x8000_0000)
  logic nl_addr_ok;
  assign nl_addr_ok = nl_target[31];  // bit 31 set → RAM region

  // Prefetch pending register
  always_ff @(posedge clk_i) begin
    if (!rst_ni || fe_flush_cache_i) begin
      pf_valid <= 1'b0;
      // pf_addr: no reset — guarded by pf_valid
    end else if (miss_detected && !pf_valid && nl_addr_ok) begin
      pf_valid <= 1'b1;
      pf_addr  <= nl_target;
    end else if (pf_fire) begin
      pf_valid <= 1'b0;
    end
  end

  // Prefetch can fire when: LD port is idle, no demand load pending,
  // no flush, and prefetcher has a request
  assign pf_ready = !load_req_fire && !load_active && !pf_active && !load_pending && !uc_drain_pending && !fe_flush_cache_i && ld_dcache_res.ready;

  assign pf_fire  = pf_valid && pf_ready;

  // Debug counters (simulation only)
  int unsigned dbg_nlp_miss, dbg_nlp_issued;
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      dbg_nlp_miss   <= 0;
      dbg_nlp_issued <= 0;
    end else begin
      if (miss_detected) dbg_nlp_miss <= dbg_nlp_miss + 1;
      if (pf_fire) dbg_nlp_issued <= dbg_nlp_issued + 1;
    end
  end
  // synthesis translate_off
  final begin
    $display("[NEXTLINE_PF] misses_seen=%0d pf_issued=%0d", dbg_nlp_miss, dbg_nlp_issued);
  end
  // synthesis translate_on

  // -------------------------------------------------------------------
  // LD-port request (loads + uncached reads + prefetch)
  // -------------------------------------------------------------------
  always_comb begin
    if (load_req_fire) begin
      ld_dcache_req.valid    = 1'b1;
      ld_dcache_req.addr     = ex_data_req_i.addr;
      ld_dcache_req.ready    = 1'b1;
      ld_dcache_req.rw       = 1'b0;
      ld_dcache_req.rw_size  = ex_data_req_i.rw_size;
      ld_dcache_req.data     = '0;
      ld_dcache_req.uncached = uncached;
    end else if (pf_fire) begin
      // Prefetch: read a full cache line (WORD-sized read, cached)
      ld_dcache_req.valid    = 1'b1;
      ld_dcache_req.addr     = pf_addr;
      ld_dcache_req.ready    = 1'b1;
      ld_dcache_req.rw       = 1'b0;
      ld_dcache_req.rw_size  = WORD;
      ld_dcache_req.data     = '0;
      ld_dcache_req.uncached = 1'b0;
    end else begin
      ld_dcache_req.valid    = 1'b0;
      ld_dcache_req.addr     = ex_data_req_i.addr;
      ld_dcache_req.ready    = 1'b1;
      ld_dcache_req.rw       = 1'b0;
      ld_dcache_req.rw_size  = ex_data_req_i.rw_size;
      ld_dcache_req.data     = '0;
      ld_dcache_req.uncached = uncached;
    end
  end

  // -------------------------------------------------------------------
  // ST-port request (SB drains + uncached stores)
  // -------------------------------------------------------------------
  always_comb begin
    if (uc_store_fire) begin
      st_dcache_req.valid    = 1'b1;
      st_dcache_req.addr     = uc_drain_pending ? uc_addr_q : ex_data_req_i.addr;
      st_dcache_req.ready    = 1'b1;
      st_dcache_req.rw       = 1'b1;
      st_dcache_req.rw_size  = uc_drain_pending ? uc_size_q : ex_data_req_i.rw_size;
      st_dcache_req.data     = uc_drain_pending ? uc_data_q : ex_data_req_i.data;
      st_dcache_req.uncached = 1'b1;
    end else if (drain_fire) begin
      st_dcache_req.valid    = 1'b1;
      st_dcache_req.addr     = sb_drain_addr;
      st_dcache_req.ready    = 1'b1;
      st_dcache_req.rw       = 1'b1;
      st_dcache_req.rw_size  = sb_drain_size;
      st_dcache_req.data     = sb_drain_data;
      st_dcache_req.uncached = sb_drain_uncached;
    end else begin
      st_dcache_req.valid    = 1'b0;
      st_dcache_req.addr     = '0;
      st_dcache_req.ready    = 1'b1;
      st_dcache_req.rw       = 1'b0;
      st_dcache_req.rw_size  = WORD;
      st_dcache_req.data     = '0;
      st_dcache_req.uncached = 1'b0;
    end
  end

  // -------------------------------------------------------------------
  // Stall generation
  // -------------------------------------------------------------------
  // Fence.i: drain store buffer before flushing dcache
  logic fencei_pending;
  logic dcache_fencei_stall;
  logic dcache_pipes_idle;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      fencei_pending <= 1'b0;
    end else begin
      if (fe_flush_cache_i && (!sb_empty || !dcache_pipes_idle)) fencei_pending <= 1'b1;
      else if (fencei_pending && sb_empty && dcache_pipes_idle) fencei_pending <= 1'b0;
    end
  end

  logic dcache_flush;
  assign dcache_flush = (fe_flush_cache_i || fencei_pending) && sb_empty && dcache_pipes_idle;

  // Load blocked on first cycle (hard conflict / dcache busy) — combinational
  // Partial overlap still needs to stall if the LD port is busy, so that
  // partial SB data can be captured before the SB entries drain away.
  logic first_cycle_load_blocked;
  assign first_cycle_load_blocked = is_load && new_req && !sb_fwd_hit && (sb_fwd_conflict || ld_port_busy || uc_drain_pending);

  // Pending load stalls unless resolved by forwarding this cycle
  logic load_stall_pending;
  assign load_stall_pending = load_pending && !load_fwd_resolve;

  always_comb begin
    dmiss_stall_o = load_req_fire
                  || (load_active && !ld_dcache_res.valid)
                  || first_cycle_load_blocked
                  || load_stall_pending
                  || (cached_store_fire && sb_full)
                  || store_pending
                  || uncached_store_fire
                  || uc_drain_pending
                  || (uc_store_active && !st_dcache_res.valid)
                  || fencei_pending;
  end

  assign fencei_stall_o = dcache_fencei_stall || fencei_pending || (fe_flush_cache_i && (!sb_empty || !dcache_pipes_idle));

  // Fence.i debug logger — Enable with: +define+LOG_FENCEI_DEBUG
  // synthesis translate_off
`ifdef LOG_FENCEI_DEBUG
  logic fencei_dbg_prev_mem;
  always_ff @(posedge clk_i) begin
    if (!rst_ni) fencei_dbg_prev_mem <= 1'b0;
    else fencei_dbg_prev_mem <= fe_flush_cache_i;
  end
  always_ff @(posedge clk_i) begin
    if (rst_ni && fe_flush_cache_i) begin
      // Log first cycle
      if (!fencei_dbg_prev_mem)
        $display("[FENCEI-DBG][MEM] %0t FENCE.I ENTER sb_empty=%b pipes_idle=%b dcache_fi_stall=%b fencei_pending=%b", $time, sb_empty, dcache_pipes_idle, dcache_fencei_stall, fencei_pending);
      // Log state every 50 cycles during fence.i
      if ($time % 50 == 0)
        $display(
            "[FENCEI-DBG][MEM] %0t STATUS sb_empty=%b pipes_idle=%b dcache_fi_stall=%b fencei_pending=%b dcache_flush=%b drain_fire=%b drain_active=%b st_port_busy=%b sb_drain_valid=%b st_ready=%b",
            $time,
            sb_empty,
            dcache_pipes_idle,
            dcache_fencei_stall,
            fencei_pending,
            dcache_flush,
            drain_fire,
            drain_active,
            st_port_busy,
            sb_drain_valid,
            st_dcache_res.ready
        );
      // Log drain events
      if (drain_fire) $display("[FENCEI-DBG][MEM] %0t SB_DRAIN addr=%08x data=%08x size=%0d", $time, sb_drain_addr, sb_drain_data, sb_drain_size);
      // Log when store buffer empties during fence.i
      if (!sb_empty && fencei_dbg_prev_mem) begin
      end  // suppress unused
    end
  end
  // Log sb_empty transition
  logic sb_empty_prev;
  always_ff @(posedge clk_i) begin
    if (!rst_ni) sb_empty_prev <= 1'b1;
    else sb_empty_prev <= sb_empty;
  end
  always_ff @(posedge clk_i) begin
    if (rst_ni && fe_flush_cache_i && !sb_empty_prev && sb_empty) $display("[FENCEI-DBG][MEM] %0t SB NOW EMPTY", $time);
    if (rst_ni && fe_flush_cache_i && dcache_flush && !fencei_dbg_prev_mem) $display("[FENCEI-DBG][MEM] %0t DCACHE_FLUSH ASSERTED (sb_empty=%b pipes_idle=%b)", $time, sb_empty, dcache_pipes_idle);
  end
`endif
  // synthesis translate_on

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
  // D-cache (dual-port non-blocking)
  // -------------------------------------------------------------------
  dcache_nb #(
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
      .ld_req_i      (ld_dcache_req),
      .ld_res_o      (ld_dcache_res),
      .st_req_i      (st_dcache_req),
      .st_res_o      (st_dcache_res),
      .lowX_res_i    (lx_dres_i),
      .lowX_req_o    (lx_dreq_o),
      .fencei_stall_o(dcache_fencei_stall),
      .pipes_idle_o  (dcache_pipes_idle)
  );

`ifdef LOG_CACHE
  cache_logger i_cache_logger (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .cache_req_i(ld_dcache_req),
      .cache_res_i(ld_dcache_res)
  );
`endif

  // -------------------------------------------------------------------
  // Uncached store transaction logger (LOG_UC_STORE=1)
  // -------------------------------------------------------------------
`ifdef LOG_UC_STORE
  // synthesis translate_off
  integer uc_log_fd;
  string  uc_log_path;

  // Transaction counters
  int unsigned uc_started, uc_completed;
  // Stuck watchdog
  int unsigned uc_active_cycles;
  localparam int UC_STUCK_THRESH = 1000;

  // Edge detectors (previous-cycle values)
  logic uc_store_fire_q, uc_store_active_q, st_dcache_res_valid_q;
  logic st_bypass_active_prev;

  initial begin
    if (!$value$plusargs("uc_store_log=%s", uc_log_path)) uc_log_path = "uc_store_trace.log";
    uc_log_fd = $fopen(uc_log_path, "w");
    if (uc_log_fd == 0) $display("[UC_STORE_LOG] ERROR: Cannot open %s", uc_log_path);
    else begin
      $display("[UC_STORE_LOG] Writing to: %s", uc_log_path);
      $fwrite(uc_log_fd, "# Uncached Store Transaction Trace\n");
      $fwrite(uc_log_fd, "# pipe_st: 0=IDLE 1=TAG_LOOKUP 2=HIT_RESPOND 3=BYPASS\n");
      $fwrite(uc_log_fd, "# mem_st:  0=MEM_IDLE 1=MEM_WB_SEND 2=MEM_FILL_SEND\n");
      $fwrite(uc_log_fd, "#\n");
      $fflush(uc_log_fd);
    end
  end

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      uc_started            <= 0;
      uc_completed          <= 0;
      uc_active_cycles      <= 0;
      uc_store_fire_q       <= 1'b0;
      uc_store_active_q     <= 1'b0;
      st_dcache_res_valid_q <= 1'b0;
      st_bypass_active_prev <= 1'b0;
    end else if (uc_log_fd != 0) begin
      // Edge detectors
      uc_store_fire_q       <= uc_store_fire;
      uc_store_active_q     <= uc_store_active;
      st_dcache_res_valid_q <= st_dcache_res.valid;
      st_bypass_active_prev <= i_dcache.st_bypass_active;

      // Stuck watchdog
      if (uc_store_active) uc_active_cycles <= uc_active_cycles + 1;
      else uc_active_cycles <= 0;

      // --- Event markers ---

      // [UC_REQ] — uc_store_fire rising edge
      if (uc_store_fire && !uc_store_fire_q) begin
        uc_started <= uc_started + 1;
        $fwrite(uc_log_fd, "%0t [UC_REQ] addr=%08x data=%08x size=%0d sb_empty=%b st_port_busy=%b uc_drain_pend=%b\n", $time, uc_drain_pending ? uc_addr_q : ex_data_req_i.addr,
                uc_drain_pending ? uc_data_q : ex_data_req_i.data, int'(uc_drain_pending ? uc_size_q : ex_data_req_i.rw_size), sb_empty, st_port_busy, uc_drain_pending);
        $fflush(uc_log_fd);
      end

      // [UC_BYPASS_ENTER] — st_pipe_state transitions to PIPE_BYPASS
      if (i_dcache.st_bypass_active && !st_bypass_active_prev) begin
        $fwrite(uc_log_fd, "%0t [UC_BYPASS_ENTER] pipe_st=%0d\n", $time, int'(i_dcache.st_pipe_state));
        $fflush(uc_log_fd);
      end

      // [UC_LOWX_OUT] — lowX request going out for uncached store
      if (lx_dreq_o.valid && lx_dreq_o.uncached && lx_dreq_o.rw) begin
        $fwrite(uc_log_fd, "%0t [UC_LOWX_OUT] addr=%08x rw=%b uncached=%b mem_st=%0d\n", $time, lx_dreq_o.addr, lx_dreq_o.rw, lx_dreq_o.uncached, int'(i_dcache.mem_state));
        $fflush(uc_log_fd);
      end

      // [UC_LOWX_RESP] — lowX response while bypass active
      if (lx_dres_i.valid && i_dcache.st_bypass_active) begin
        $fwrite(uc_log_fd, "%0t [UC_LOWX_RESP] data[31:0]=%08x ld_bypass=%b fi_wb=%b pipe_st=%0d\n", $time, lx_dres_i.data[31:0], i_dcache.ld_bypass_active, i_dcache.fi_writeback_req,
                int'(i_dcache.st_pipe_state));
        $fflush(uc_log_fd);
      end

      // [UC_DONE] — st_dcache_res.valid clears uc_store_active
      if (st_dcache_res.valid && uc_store_active) begin
        uc_completed <= uc_completed + 1;
        $fwrite(uc_log_fd, "%0t [UC_DONE] cycles=%0d pipe_st=%0d\n", $time, uc_active_cycles, int'(i_dcache.st_pipe_state));
        $fflush(uc_log_fd);
      end

      // [UC_STUCK] — uc_store_active held too long
      if (uc_active_cycles == UC_STUCK_THRESH) begin
        $fwrite(uc_log_fd, "%0t [UC_STUCK] uc_active=%b st_res_v=%b bypass=%b pipe_st=%0d mem_st=%0d lowX_req_v=%b lowX_res_v=%b drain_a=%b uc_pend=%b stall=%b\n", $time, uc_store_active,
                st_dcache_res.valid, i_dcache.st_bypass_active, int'(i_dcache.st_pipe_state), int'(i_dcache.mem_state), lx_dreq_o.valid, lx_dres_i.valid, drain_active, uc_drain_pending,
                dmiss_stall_o);
        $fflush(uc_log_fd);
      end

      // --- Per-cycle trace (only when any UC signal is active) ---
      if (uc_store_fire || uc_store_active || uncached_store_fire || uc_drain_pending || (i_dcache.st_bypass_active && i_dcache.st_req_q.uncached)) begin
        $fwrite(
            uc_log_fd,
            "%0t | uc_sfire=%b uc_active=%b st_req_v=%b st_res_v=%b st_res_rdy=%b bypass=%b pipe_st=%0d mem_st=%0d lowX_req_v=%b lowX_res_v=%b lowX_d=%08x drain_a=%b drain_f=%b uc_pend=%b st_busy=%b stall=%b | addr=%08x\n",
            $time, uc_store_fire, uc_store_active, st_dcache_req.valid, st_dcache_res.valid, st_dcache_res.ready, i_dcache.st_bypass_active, int'(i_dcache.st_pipe_state), int'(i_dcache.mem_state),
            lx_dreq_o.valid, lx_dres_i.valid, lx_dres_i.data[31:0], drain_active, drain_fire, uc_drain_pending, st_port_busy, dmiss_stall_o, st_dcache_req.valid ? st_dcache_req.addr : 32'h0);
        $fflush(uc_log_fd);
      end
    end
  end

  final begin
    if (uc_log_fd != 0) begin
      $fwrite(uc_log_fd, "\n# === SUMMARY ===\n");
      $fwrite(uc_log_fd, "# uc_stores_started  = %0d\n", uc_started);
      $fwrite(uc_log_fd, "# uc_stores_completed = %0d\n", uc_completed);
      $fwrite(uc_log_fd, "# uc_stores_hung      = %0d\n", uc_started - uc_completed);
      $fclose(uc_log_fd);
    end
    $display("[UC_STORE_LOG] started=%0d completed=%0d hung=%0d", uc_started, uc_completed, uc_started - uc_completed);
  end
  // synthesis translate_on
`endif

  // -------------------------------------------------------------------
  // Read data: forwarded from store buffer OR from dcache
  // Supports full forwarding, partial merge, and dcache-only paths.
  // -------------------------------------------------------------------
  logic [     7:0] selected_byte;
  logic [    15:0] selected_halfword;

  // Latch dcache response data — dcache_nb's ld_res_o.valid is a single-cycle
  // pulse.  The pipeline needs the data to persist until pipe3 captures it.
  logic [XLEN-1:0] ld_data_q;
  logic            ld_data_valid_q;

  always_ff @(posedge clk_i) begin
    if (!rst_ni || fe_flush_cache_i) begin
      // ld_data_q: no reset — guarded by ld_data_valid_q
      ld_data_valid_q <= 1'b0;
    end else if (ld_dcache_res.valid) begin
      ld_data_q       <= ld_dcache_res.data;
      ld_data_valid_q <= 1'b1;
    end else if (load_req_fire) begin
      ld_data_valid_q <= 1'b0;
    end
  end

  // Select between live dcache output and latched data
  logic [XLEN-1:0] ld_data_mux;
  assign ld_data_mux = ld_dcache_res.valid ? ld_dcache_res.data : ld_data_q;

  // Latch SB-forwarded data — the entry may drain before pipe3 captures me_data_o.
  // When a load has SB-forwarded data but the pipeline can't advance (IMISS_STALL),
  // hold the forwarded value so it persists until pipe3 captures it.
  logic [XLEN-1:0] sb_fwd_data_q;
  logic            sb_fwd_hold_q;

  always_ff @(posedge clk_i) begin
    if (!rst_ni || fe_flush_cache_i) begin
      // sb_fwd_data_q: no reset — guarded by sb_fwd_hold_q
      sb_fwd_hold_q <= 1'b0;
    end else if (is_load && sb_fwd_hit && !sb_fwd_conflict) begin
      // Capture SB forward data every cycle the forward is valid
      sb_fwd_data_q <= sb_fwd_data;
      sb_fwd_hold_q <= 1'b1;
    end else if (!is_load || new_req) begin
      // Clear when no longer a load or a new different request appears
      sb_fwd_hold_q <= 1'b0;
    end
  end

  // Latched SB partial data and mask for merging with dcache response
  logic [XLEN-1:0] sb_partial_data_q;
  logic [     3:0] sb_partial_mask_q;

  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      // sb_partial_data_q: no reset — guarded by sb_partial_mask_q
      sb_partial_mask_q <= '0;
    end else if ((load_req_fire || first_cycle_load_blocked) && sb_fwd_partial) begin
      sb_partial_data_q <= sb_fwd_partial_data;
      sb_partial_mask_q <= sb_fwd_byte_mask;
    end else if ((ld_dcache_res.valid && load_active) || fe_flush_cache_i) begin
      sb_partial_mask_q <= '0;
    end
  end

  always_comb begin : read_data_size_handler
    // Full SB hit: use SB data directly (live or held)
    if (is_load && sb_fwd_hit && !sb_fwd_conflict) begin
      rd_data = sb_fwd_data;
    end else if (is_load && sb_fwd_hold_q && !load_active) begin
      // SB entry was drained but we still have the forwarded data latched
      rd_data = sb_fwd_data_q;
    end  // Partial merge: combine latched SB bytes with dcache response
    else if (load_partial_q) begin
      for (int b = 0; b < 4; b++) begin
        rd_data[b*8+:8] = sb_partial_mask_q[b] ? sb_partial_data_q[b*8+:8] : ld_data_mux[b*8+:8];
      end
    end  // Default: dcache only (use latched data when available)
    else begin
      rd_data = ld_data_mux;
    end

    me_data_o         = '0;

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
