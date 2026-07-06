// ============================================================================
// Level RISC-V — UVM Testbench Üst Modülü
// ----------------------------------------------------------------------------
// DUT sınırı: `cpu` çekirdeği (5 aşamalı boru hattı + L1/L2 önbellek +
// memory_arbiter). SoC sarmalayıcı (Wishbone, periferikler) BİLEREK dışarıda
// bırakıldı: çekirdeğin tek bellek kapısı (iomem) ve 3 kesme pini, UVM
// agent'larının tam kontrolünde — rastgele gecikme/backpressure ancak böyle
// serbestçe uygulanabilir.
//
// Görevleri:
//   * Saat/reset üretimi (UVM'e dahil edilmeyen tek "prosedürel" iş),
//   * Interface örnekleri + DUT struct portlarına köprüleme,
//   * `bind cpu` ile commit_if enjeksiyonu (RTL değişikliği sıfır),
//   * Sanal arayüzleri uvm_config_db'ye kayıt,
//   * run_test() ile UVM'i başlatma.
// ============================================================================
`timescale 1ns / 1ps
`include "level_defines.svh"

// Commit gözlem arayüzünü çekirdeğin İÇİNE enjekte et. Port bağlantıları
// cpu.sv'nin dahili sinyallerine bind kapsamında doğrudan erişir:
//   wb_rf_rw  : WB aşamasının nihai register-yazma enable'ı
//   pipe4.*   : MEM->WB boru hattı register'ı
//   wb_data   : WB yazma verisi mux çıkışı
bind cpu commit_if u_commit_if (
    .clk     (clk_i),
    .rst_n   (rst_ni),
    .rf_we   (wb_rf_rw),
    .rd_addr (pipe4.rd_addr),
    .rd_wdata(wb_data),
    .pc_incr (pipe4.pc_incr)
);

module level_v_tb_top;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import level_param::*;      // iomem_req_t / iomem_res_t struct tipleri
  import level_v_uvm_pkg::*;  // testbench sınıfları

  // --------------------------------------------------------------------------
  // Saat ve reset
  // --------------------------------------------------------------------------
  // 100 MHz varsayılan; +clk_period_ps=<ps> ile değiştirilebilir.
  int unsigned clk_period_ps = 10_000;
  logic clk = 1'b0;
  logic rst_n = 1'b0;

  initial begin
    void'($value$plusargs("clk_period_ps=%d", clk_period_ps));
    forever #(clk_period_ps / 2 * 1ps) clk = ~clk;
  end

  // Reset: 20 çevrim aktif — önbellek/BP dizilerinin sıfırlanması için bol.
  initial begin
    rst_n = 1'b0;
    repeat (20) @(posedge clk);
    rst_n = 1'b1;
    `uvm_info("TB_TOP", "Reset birakildi", UVM_LOW)
  end

  // --------------------------------------------------------------------------
  // Interface örnekleri
  // --------------------------------------------------------------------------
  iomem_if mem_if_i (.clk(clk), .rst_n(rst_n));
  irq_if   irq_if_i (.clk(clk), .rst_n(rst_n));

  // --------------------------------------------------------------------------
  // DUT ve struct <-> interface köprüsü
  // --------------------------------------------------------------------------
  iomem_req_t iomem_req;
  iomem_res_t iomem_res;

  cpu dut (
      .clk_i      (clk),
      .rst_ni     (rst_n),
      .timer_irq_i(irq_if_i.timer_irq),
      .sw_irq_i   (irq_if_i.sw_irq),
      .ext_irq_i  (irq_if_i.ext_irq),
      .iomem_req_o(iomem_req),
      .iomem_res_i(iomem_res)
  );

  // İstek yönü: DUT struct'ı -> interface sinyalleri (monitör örneklesin)
  assign mem_if_i.req_valid    = iomem_req.valid;
  assign mem_if_i.req_ready    = iomem_req.ready;
  assign mem_if_i.req_rw       = iomem_req.rw;
  assign mem_if_i.req_addr     = iomem_req.addr;
  assign mem_if_i.req_data     = iomem_req.data;
  assign mem_if_i.req_uncached = iomem_req.uncached;

  // Yanıt yönü: interface (driver sürer) -> DUT struct'ı
  assign iomem_res.valid = mem_if_i.res_valid;
  assign iomem_res.ready = mem_if_i.res_ready;
  assign iomem_res.data  = mem_if_i.res_data;

  // --------------------------------------------------------------------------
  // Sanal arayüz kayıtları + UVM başlatma
  // --------------------------------------------------------------------------
  initial begin
    // "uvm_test_top.*" yerine "*": env hiyerarşi adından bağımsız kalsın.
    uvm_config_db#(virtual iomem_if)::set(null, "*", "mem_vif", mem_if_i);
    uvm_config_db#(virtual irq_if)::set(null, "*", "irq_vif", irq_if_i);
    // bind ile enjekte edilen örneğe hiyerarşik referans — standart yol.
    uvm_config_db#(virtual commit_if)::set(null, "*", "commit_vif",
                                           dut.u_commit_if);
    run_test();  // +UVM_TESTNAME ile test seçilir
  end

  // --------------------------------------------------------------------------
  // Dalga kaydı (opsiyonel): +lv_wave=<dosya.vcd>
  // --------------------------------------------------------------------------
  initial begin
    string wf;
    if ($value$plusargs("lv_wave=%s", wf)) begin
      $dumpfile(wf);
      $dumpvars(0, level_v_tb_top);
    end
  end

endmodule : level_v_tb_top
