// ============================================================================
// Level RISC-V UVM — Commit (Retire) Monitörü
// ----------------------------------------------------------------------------
// tb_top'un `bind cpu` ile çekirdeğin içine yerleştirdiği commit_if'i izler.
// Register dosyasına yazan her emekli komut için bir commit_item yayınlar.
//
// Kullanıcıları:
//   * Scoreboard : watchdog beslemesi (çekirdek canlı mı?) + trace dosyası
//   * Coverage   : rd dağılımı, yazılan değer uçları
//
// Not: Store/branch gibi register yazmayan komutlar burada görünmez; canlılık
// tespiti için bu yeterlidir çünkü hiç register yazmadan sonsuza kadar koşan
// gerçekçi bir program yoktur (self-loop dahi PC ilerletir ama rf yazmaz —
// bu yüzden watchdog süresi programın bitiş self-loop süresini tolere edecek
// şekilde tohost yazımıyla birlikte değerlendirilir, bkz. scoreboard).
// ============================================================================

// Tek bir register-yazan commit'in kaydı.
class commit_item extends uvm_sequence_item;

  bit [ 4:0] rd_addr;
  bit [31:0] rd_wdata;
  bit [31:0] pc_incr;   // Emekli komutun PC+4/+2 değeri (PC yaklaşıklığı)
  time       ts;

  `uvm_object_utils_begin(commit_item)
    `uvm_field_int(rd_addr,  UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(rd_wdata, UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(pc_incr,  UVM_DEFAULT | UVM_HEX)
  `uvm_object_utils_end

  function new(string name = "commit_item");
    super.new(name);
  endfunction

  function string convert2string();
    return $sformatf("pc_incr=0x%08h x%0d <= 0x%08h", pc_incr, rd_addr, rd_wdata);
  endfunction

endclass : commit_item


class commit_monitor extends uvm_component;

  `uvm_component_utils(commit_monitor)

  virtual commit_if vif;
  uvm_analysis_port #(commit_item) commit_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    commit_ap = new("commit_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual commit_if)::get(this, "", "commit_vif", vif))
      `uvm_fatal("CMT_MON", "commit_if sanal arayuzu config_db'de yok (bind basarisiz olabilir)")
  endfunction

  task run_phase(uvm_phase phase);
    commit_item it;
    @(posedge vif.rst_n);
    forever begin
      @(vif.mon_cb);
      // rf_we, WB aşamasında downstream stall ve fence.i flush maskelemesi
      // uygulanmış NİHAİ yazma enable'ıdır (writeback.sv) — x0 yazmaları da
      // RTL'de üretilmez varsayımıyla filtre eklemiyoruz; gelirse coverage'da
      // görünür ve tartışılır (x0 mimari olarak zararsızdır).
      if (vif.mon_cb.rf_we) begin
        it          = commit_item::type_id::create("commit");
        it.rd_addr  = vif.mon_cb.rd_addr;
        it.rd_wdata = vif.mon_cb.rd_wdata;
        it.pc_incr  = vif.mon_cb.pc_incr;
        it.ts       = $time;
        commit_ap.write(it);
      end
    end
  endtask

endclass : commit_monitor
