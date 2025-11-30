`timescale 1ns / 1ps
`include "ceres_defines.svh"

module memory
  import ceres_param::*;
(
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  stall_e                stall_i,
    input  logic                  fe_flush_cache_i,
    input  dlowX_res_t            lx_dres_i,
    output dlowX_req_t            lx_dreq_o,
    output logic       [XLEN-1:0] me_data_o,
    output logic                  dmiss_stall_o,
    output logic                  fencei_stall_o,    // Dcache dirty writeback stall for fence.i
    output logic                  uart_tx_o,
    input  logic                  uart_rx_i,
    // MEM stage view (pipe3)
    input  data_req_t             me_data_req_i,
    // EX stage view (pipe2)
    input  data_req_t             ex_data_req_i
);

  dcache_req_t            dcache_req;
  dcache_res_t            dcache_res;
  logic        [XLEN-1:0] pherip_addr;
  logic        [XLEN-1:0] pherip_wdata;
  logic        [     3:0] pherip_sel;
  logic        [XLEN-1:0] pherip_rdata;
  logic                   pherip_valid;
  logic        [XLEN-1:0] rd_data;
  logic                   uncached;
  logic                   memregion;
  logic                   grand;
  logic                   mem_txn_active;  // "request in flight" flag
  logic                   mem_req_fire;  // this cycle we start a new cache request

  // Yalnızca ex_data_req_i.valid 0→1 olduğunda (yükselen kenar) ve
  // aktif transaction yokken yeni istek başlat.


  logic                   ex_valid_q;
  logic        [XLEN-1:0] ex_addr_q;
  logic                   ex_rw_q;
  logic        [     1:0] ex_rw_size_q;

  always_ff @(posedge clk_i) begin
    if (!rst_ni || fe_flush_cache_i) begin
      ex_valid_q   <= 1'b0;
      ex_addr_q    <= '0;
      ex_rw_q      <= 1'b0;
      ex_rw_size_q <= '0;
    end else begin
      ex_valid_q   <= ex_data_req_i.valid;
      ex_addr_q    <= ex_data_req_i.addr;
      ex_rw_q      <= ex_data_req_i.rw;
      ex_rw_size_q <= ex_data_req_i.rw_size;
    end
  end

  // Start a new memory transaction when the input request is valid and
  // differs from the previous captured request, and there is no active
  // transaction for the memory region. This handles consecutive requests
  // whose `valid` may remain asserted across cycles (addresses/data change).
  // NOTE: We intentionally exclude .data from comparison to break combinational
  // loop: ex_data_req.data depends on forwarding which depends on stall_cause
  // which depends on dmiss_stall which depends on mem_req_fire.
  logic req_changed;
  assign req_changed  = (ex_data_req_i.addr != ex_addr_q) || (ex_data_req_i.rw != ex_rw_q) || (ex_data_req_i.rw_size != ex_rw_size_q) || (ex_data_req_i.valid && !ex_valid_q);
  assign mem_req_fire = ex_data_req_i.valid && req_changed && memregion && !mem_txn_active;

  always_ff @(posedge clk_i) begin
    if (!rst_ni || fe_flush_cache_i) begin
      mem_txn_active <= 1'b0;
    end else begin
      if (dcache_res.valid) begin
        mem_txn_active <= 1'b0;
      end
      if (mem_req_fire) begin
        mem_txn_active <= 1'b1;
      end
    end
  end

  always_comb begin
    dcache_req.valid    = mem_req_fire;
    dcache_req.addr     = ex_data_req_i.addr;
    dcache_req.ready    = 1'b1;
    dcache_req.rw       = ex_data_req_i.rw;
    dcache_req.rw_size  = ex_data_req_i.rw_size;
    dcache_req.data     = ex_data_req_i.data;
    dcache_req.uncached = uncached;

    if (memregion) begin
      dmiss_stall_o = mem_req_fire || (mem_txn_active && !dcache_res.valid);
    end else begin
      dmiss_stall_o = 1'b0;
    end
  end

  pma i_dpma (
      .addr_i     (ex_data_req_i.addr),
      .uncached_o (uncached),
      .memregion_o(memregion),
      .grand_o    (grand)
  );

  cache #(
      .IS_ICACHE  (0),
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
      .flush_i       (fe_flush_cache_i),
      .cache_req_i   (dcache_req),
      .cache_res_o   (dcache_res),
      .lowX_res_i    (lx_dres_i),
      .lowX_req_o    (lx_dreq_o),
      .fencei_stall_o(fencei_stall_o)
  );

  logic [ 7:0] selected_byte;
  logic [15:0] selected_halfword;

  always_comb begin : read_data_size_handler
    rd_data           = !memregion ? pherip_rdata : dcache_res.data;
    me_data_o         = '0;

    // adresin low bitlerine göre byte/halfword seçimi
    selected_byte     = rd_data[(ex_data_req_i.addr[1:0]*8)+:8];
    selected_halfword = rd_data[(ex_data_req_i.addr[1]*16)+:16];

    // load size + signed/unsigned
    unique case (ex_data_req_i.rw_size)
      2'b01:   me_data_o = ex_data_req_i.ld_op_sign ? {{24{selected_byte[7]}}, selected_byte} : {24'b0, selected_byte};
      2'b10:   me_data_o = ex_data_req_i.ld_op_sign ? {{16{selected_halfword[15]}}, selected_halfword} : {16'b0, selected_halfword};
      2'b11:   me_data_o = rd_data;
      default: me_data_o = '0;
    endcase
  end

  always_comb begin
    pherip_valid = !memregion && !fe_flush_cache_i && !(stall_i inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL});
    pherip_addr  = !memregion ? ex_data_req_i.addr : '0;
    pherip_sel   = !memregion && !fe_flush_cache_i && !(stall_i inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL}) ? 4'b1111 : 4'b0000;
    pherip_wdata = !memregion ? ex_data_req_i.data : '0;
  end

  uart i_uart (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .stb_i     (pherip_valid),
      .adr_i     (pherip_addr[3:2]),
      .byte_sel_i(pherip_sel),
      .we_i      (ex_data_req_i.rw),
      .dat_i     (pherip_wdata),
      .dat_o     (pherip_rdata),
      .uart_rx_i (uart_rx_i),
      .uart_tx_o (uart_tx_o)
  );

endmodule
