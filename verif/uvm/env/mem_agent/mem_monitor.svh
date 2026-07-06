// ============================================================================
// Level RISC-V UVM — Bellek Monitörü
// ----------------------------------------------------------------------------
// iomem arayüzünü tamamen PASİF izler ve iki ayrı analysis port'tan yayın
// yapar:
//
//   req_ap : İstek İLK görüldüğü anda (yanıt beklemeden) yayınlanır.
//            Hedefi sequencer'daki req_fifo'dur -> responder sequence bu
//            sayede yanıtı hazırlamaya hemen başlar.
//   txn_ap : İstek + yanıt TAMAMLANDIĞINDA, gecikme ölçümüyle birlikte
//            yayınlanır. Hedefi scoreboard ve coverage collector'dır.
//
// Protokol tek-bekleyen-işlem (single outstanding) olduğundan durum makinesi
// basittir: busy bayrağı, istek görülünce kalkar, res_valid ile düşer.
// İstek yanıtla AYNI çevrimde de sonlanabilir (min gecikmede) — sıralama
// buna göre kurgulanmıştır: önce tamamlama, sonra yeni istek kontrolü.
// ============================================================================

class mem_monitor extends uvm_component;

  `uvm_component_utils(mem_monitor)

  virtual iomem_if vif;
  mem_agent_cfg    cfg;

  uvm_analysis_port #(mem_txn) req_ap;  // ham istekler -> sequencer FIFO
  uvm_analysis_port #(mem_txn) txn_ap;  // tamamlanmış işlemler -> sb/cov

  function new(string name, uvm_component parent);
    super.new(name, parent);
    req_ap = new("req_ap", this);
    txn_ap = new("txn_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual iomem_if)::get(this, "", "mem_vif", vif))
      `uvm_fatal("MEM_MON", "iomem_if sanal arayuzu config_db'de yok")
    if (!uvm_config_db#(mem_agent_cfg)::get(this, "", "mem_cfg", cfg))
      `uvm_fatal("MEM_MON", "mem_agent_cfg config_db'de yok")
  endfunction

  task run_phase(uvm_phase phase);
    mem_txn cur;              // Uçuştaki (in-flight) işlem
    bit     busy = 0;         // 1 -> istek görüldü, yanıt bekleniyor
    int unsigned lat_cnt = 0; // Gecikme sayacı (çevrim)

    @(posedge vif.rst_n);

    forever begin
      @(vif.mon_cb);

      // 1) Tamamlama kontrolü: uçuştaki işlem bu çevrimde yanıt aldı mı?
      if (busy && vif.mon_cb.res_valid) begin
        cur.rdata    = vif.mon_cb.res_data;
        cur.latency  = lat_cnt;
        cur.rsp_time = $time;
        `uvm_info("MEM_MON", {"Tamamlandi: ", cur.convert2string()}, UVM_HIGH)
        txn_ap.write(cur);
        busy = 0;
      end

      // 2) Yeni istek kontrolü: valid yüksek ve uçuşta işlem yok.
      //    DİKKAT: res_valid'in yüksek olduğu çevrimde req_valid hâlâ
      //    TAMAMLANAN işleme aittir (arbiter kilidini bir sonraki çevrimde
      //    temizler). Bu yüzden aynı çevrimde yeni istek yakalamayız —
      //    aksi halde biten işlem ikinci kez "yeni istek" sanılırdı.
      if (!busy && vif.mon_cb.req_valid && !vif.mon_cb.res_valid) begin
        cur          = mem_txn::type_id::create("txn");
        cur.addr     = vif.mon_cb.req_addr;
        cur.rw       = vif.mon_cb.req_rw;
        cur.uncached = vif.mon_cb.req_uncached;
        cur.wdata    = vif.mon_cb.req_data;
        cur.req_time = $time;
        lat_cnt      = 0;
        busy         = 1;
        `uvm_info("MEM_MON",
                  $sformatf("Istek: %s %s addr=0x%08h",
                            (cur.dir() == LV_MEM_WRITE) ? "WR" : "RD",
                            cur.uncached ? "UNC" : "CHD", cur.addr),
                  UVM_HIGH)
        // Responder sequence yanıtı hazırlayabilsin diye hemen yayınla.
        req_ap.write(cur);
      end

      if (busy) lat_cnt++;
    end
  endtask

endclass : mem_monitor
