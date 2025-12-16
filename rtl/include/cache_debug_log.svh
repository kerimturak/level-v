// ============================================================================
// Cache Debug Logging - Detailed Table Format
// Engineer: Kerim Turak
// ============================================================================
// Enable with: +define+LOG_CACHE_DEBUG
// Logs detailed cache operations in a structured table format
// ============================================================================

`ifdef LOG_CACHE_DEBUG

// Cache module is instantiated inside the cache.sv itself
// So we just use local signals, no hierarchical path needed

integer dcache_log_fd;
string  dcache_log_path;
string  dcache_test_name;
string  dcache_simulator;

initial begin
  if (!$value$plusargs("simulator=%s", dcache_simulator)) dcache_simulator = "default_simulator";

  if (!$value$plusargs("test_name=%s", dcache_test_name)) dcache_test_name = "default_test";

  if (!$value$plusargs("dcache_log_file=%s", dcache_log_path)) dcache_log_path = $sformatf("/home/kerim/level-v/results/logs/%0s/%0s/dcache_debug.log", dcache_simulator, dcache_test_name);

  void'($system($sformatf("mkdir -p $(dirname %s)", dcache_log_path)));

  dcache_log_fd = $fopen(dcache_log_path, "w");
  if (dcache_log_fd == 0) begin
    $display("[ERROR] Failed to open dcache debug log: %s", dcache_log_path);
    $finish;
  end else begin
    $display("[DCACHE_LOG] Writing to: %s", dcache_log_path);

    // Table header
    $fwrite(
        dcache_log_fd,
        "╔══════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╗\n");
    $fwrite(dcache_log_fd, "║                                            CERES RISC-V DCache Debug Log                                                             ║\n");
    $fwrite(
        dcache_log_fd,
        "╠═══════╦══════════╦══════╦══════╦═══════╦══════════╦═════════════════╦═════╦═════╦═════╦═════════╦═════════╦═════════╦════════════════╣\n");
    $fwrite(dcache_log_fd, "║ Cycle ║   Addr   ║ Hit? ║ Miss ║  WB?  ║  lowX_V  ║  lowX_R  Ready  ║ Vld ║ Rdy ║ Drty║  Tag    ║  EvTag  ║  Set    ║     Event      ║\n");
    $fwrite(
        dcache_log_fd,
        "╠═══════╬══════════╬══════╬══════╬═══════╬══════════╬═════════════════╬═════╬═════╬═════╬═════════╬═════════╬═════════╬════════════════╣\n");
  end
end

// Log dcache operations
// Note: This code should be included inside dcache_impl block where write_back is defined
always @(posedge clk_i) begin
  if (rst_ni && cache_req_q.valid) begin
    automatic logic                  hit = cache_hit;
    automatic logic                  miss = cache_miss;
    automatic logic                  wb = write_back;
    automatic logic  [         31:0] addr = cache_req_q.addr;
    automatic logic                  lowX_valid = lowX_req_o.valid;
    automatic logic                  lowX_ready = lowX_req_o.ready;
    automatic logic                  lowX_res_r = lowX_res_i.ready;
    automatic logic                  lowX_res_v = lowX_res_i.valid;
    automatic logic  [  NUM_WAY-1:0] valid_vec = cache_valid_vec;
    automatic logic  [  NUM_WAY-1:0] dirty_vec = drsram_rd_rdirty;
    automatic logic  [ TAG_SIZE-1:0] evict_tag_l = evict_tag;
    automatic logic  [ TAG_SIZE-1:0] req_tag = addr[XLEN-1:IDX_WIDTH+BOFFSET];
    automatic logic  [IDX_WIDTH-1:0] set_idx = rd_idx;
    automatic string                 event_str = "";

    // Determine event type
    if (wb && lowX_res_v) begin
      event_str = "WB_COMPLETE";
    end else if (wb) begin
      event_str = "WB_ACTIVE";
    end else if (miss && lowX_valid && lowX_res_v) begin
      event_str = "FILL_COMPLETE";
    end else if (miss && lowX_valid) begin
      event_str = "FILL_REQ";
    end else if (miss) begin
      event_str = "MISS_DETECT";
    end else if (hit && cache_req_q.rw) begin
      event_str = "HIT_WRITE";
    end else if (hit) begin
      event_str = "HIT_READ";
    end else begin
      event_str = "IDLE";
    end

    // Log entry in table format
    $fwrite(dcache_log_fd, "║ %5d ║ %08h ║  %s   ║  %s   ║   %s   ║    %b     ║   %b        %b    ║%b ║  %b  ║%b ║ %07h ║ %07h ║   %02h    ║ %-14s ║\n",
            $time / 10,  // Cycle (assuming 10ns period)
            addr,  // Address
            hit ? "Y" : "N",  // Hit?
            miss ? "Y" : "N",  // Miss?
            wb ? "Y" : "N",  // Writeback?
            lowX_valid,  // lowX valid
            lowX_ready, lowX_res_r,  // lowX ready signals
            valid_vec,  // Valid bits
            lowX_res_v,  // lowX response valid
            dirty_vec,  // Dirty bits
            req_tag,  // Request tag
            evict_tag,  // Eviction tag
            set_idx,  // Set index
            event_str  // Event description
    );
  end
end

// Log writebacks specifically
always @(posedge clk_i) begin
  if (rst_ni && write_back && lowX_req_o.valid) begin
    automatic logic [ 31:0] evict_addr = lowX_req_o.addr;
    automatic logic [127:0] evict_data = lowX_req_o.data;

    $fwrite(dcache_log_fd, "║       ║ WRITEBACK DETAIL: Evict addr=0x%08h Data=0x%032h                                                                         ║\n", evict_addr, evict_data);
  end
end

// Log fence.i events
always @(posedge clk_i) begin
  if (rst_ni && fi_active) begin
    automatic logic  [          2:0] fi_state = fi_state_q;
    automatic logic  [IDX_WIDTH-1:0] fi_set = fi_set_idx_q;
    automatic logic  [$clog2(NUM_WAY)-1:0] fi_way = fi_way_idx_q;
    automatic string                 state_name = "";

    case (fi_state)
      0:       state_name = "FI_IDLE";
      1:       state_name = "FI_SCAN";
      2:       state_name = "FI_CHECK_WAY";
      3:       state_name = "FI_WB_REQ";
      4:       state_name = "FI_WB_WAIT";
      5:       state_name = "FI_MARK_CLN";
      6:       state_name = "FI_NEXT_WAY";
      7:       state_name = "FI_DONE";
      default: state_name = "UNKNOWN";
    endcase

    $fwrite(dcache_log_fd, "║       ║ FENCE.I STATE: %-11s Set=%02h Way=%0d                                                                                     ║\n", state_name, fi_set, fi_way);
  end
end

// Periodic flush
logic [15:0] dcache_flush_counter = '0;
always @(posedge clk_i) begin
  if (rst_ni) begin
    dcache_flush_counter <= dcache_flush_counter + 1;
    if (dcache_flush_counter == 0 && dcache_log_fd != 0) begin
      $fflush(dcache_log_fd);
    end
  end
end

final begin
  if (dcache_log_fd != 0) begin
    $fwrite(
        dcache_log_fd,
        "╚═══════╩══════════╩══════╩══════╩═══════╩══════════╩═════════════════╩═════╩═════╩═════╩═════════╩═════════╩═════════╩════════════════╝\n");
    $fclose(dcache_log_fd);
  end
end

`endif  // LOG_CACHE_DEBUG
