// ============================================================================
// Level RISC-V UVM — Scoreboard
// ----------------------------------------------------------------------------
// Dört bağımsız kontrol/gözlem görevini tek component'te toplar:
//
//  1) TEST SONU TESPİTİ (tohost): Rastgele/harici program, tohost adresine
//     (UNCACHED! bkz. level_v_types.svh) yazarak biter.
//       değer == 1        -> PASS
//       değer != 1 (tek)  -> FAIL, kod = değer>>1 (riscv-tests sözleşmesi;
//                            trap handler (mcause<<1)|1 yazar)
//     Sonuç, uvm_event_pool'daki "lv_test_done" olayı ile virtual sequence
//     katmanına duyurulur (ileri düzey teknik: event tabanlı senkronizasyon —
//     vseq, objection'ı bu olayla bırakır).
//
//  2) OKUMA VERİSİ BÜTÜNLÜĞÜ: Monitörün gözlediği her okuma yanıtı, aynı
//     anda mem_model'den beklenen değerle karşılaştırılır. Responder
//     sequence -> driver -> pin -> DUT zincirindeki her bozulmayı yakalar
//     (ve callback ile bilinçli bozma yapan testlerde kapatılabilir).
//
//  3) WATCHDOG: Commit monitöründen beslenir. Çekirdek 'wd_commit_limit'
//     çevrim boyunca hiç register yazmadıysa VE bellekte de hareket yoksa
//     kilitlenme (deadlock/livelock) ilan edilir. phase_ready_to_end
//     kancasıyla da zarif bitiş desteklenir.
//
//  4) COMMIT TRACE: +lv_trace dosya yoluna Spike-benzeri satırlar yazar;
//     offline karşılaştırma/inceleme için.
// ============================================================================

`uvm_analysis_imp_decl(_sb_mem)
`uvm_analysis_imp_decl(_sb_commit)

class level_v_scoreboard extends uvm_component;

  `uvm_component_utils(level_v_scoreboard)

  uvm_analysis_imp_sb_mem    #(mem_txn,     level_v_scoreboard) mem_imp;
  uvm_analysis_imp_sb_commit #(commit_item, level_v_scoreboard) commit_imp;

  mem_agent_cfg mem_cfg;      // paylaşılan mem_model'e erişim için
  virtual iomem_if vif;       // watchdog'un çevrim saati için

  // ---- tohost ----
  bit [31:0] tohost_addr = LV_TOHOST_DEFAULT;
  bit        tohost_from_plusarg = 0;  // plusarg cfg'yi ezer (env buna bakar)
  bit        test_done   = 0;
  bit        test_passed = 0;
  bit [31:0] tohost_val  = 0;

  // ---- watchdog ----
  int unsigned wd_commit_limit = 50_000;  // commit'siz azami çevrim
  protected longint unsigned last_activity_cycle = 0;
  protected longint unsigned cycle_cnt = 0;

  // ---- istatistik ----
  int unsigned n_reads, n_writes, n_commits, n_rd_mismatch;

  // ---- trace ----
  protected int trace_fd = 0;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    mem_imp    = new("mem_imp", this);
    commit_imp = new("commit_imp", this);
  endfunction

  function void build_phase(uvm_phase phase);
    string trace_path;
    super.build_phase(phase);

    if (!uvm_config_db#(mem_agent_cfg)::get(this, "", "mem_cfg", mem_cfg))
      `uvm_fatal("SB", "mem_agent_cfg config_db'de yok")
    if (!uvm_config_db#(virtual iomem_if)::get(this, "", "mem_vif", vif))
      `uvm_fatal("SB", "iomem_if sanal arayuzu config_db'de yok")

    // Plusarg'lar komut satırından ince ayara izin verir:
    //   +tohost_addr=0x30001000  +lv_trace=commit.log  +wd_limit=100000
    begin
      string s;
      if ($value$plusargs("tohost_addr=%h", tohost_addr)) begin
        tohost_from_plusarg = 1;
        `uvm_info("SB", $sformatf("tohost adresi plusarg: 0x%08h", tohost_addr),
                  UVM_LOW)
      end
      if ($value$plusargs("wd_limit=%d", wd_commit_limit)) ;
      if ($value$plusargs("lv_trace=%s", trace_path)) begin
        trace_fd = $fopen(trace_path, "w");
        if (trace_fd == 0)
          `uvm_error("SB", {"Trace dosyasi acilamadi: ", trace_path})
        else
          `uvm_info("SB", {"Commit trace: ", trace_path}, UVM_LOW)
      end
    end
  endfunction

  // --------------------------------------------------------------------------
  // Bellek işlemi gözlemi
  // --------------------------------------------------------------------------
  function void write_sb_mem(mem_txn t);
    last_activity_cycle = cycle_cnt;

    if (t.dir() == LV_MEM_WRITE) begin
      n_writes++;
      check_tohost(t);
    end else begin
      n_reads++;
      check_read_integrity(t);
    end
  endfunction

  // tohost yazması mı? Uncached word yazmalarında adres karşılaştır.
  protected function void check_tohost(mem_txn t);
    bit [31:0] waddr_word;
    bit [31:0] wval;
    if (!t.uncached) return;
    waddr_word = {t.addr[31:2], 2'b00};
    if (waddr_word != {tohost_addr[31:2], 2'b00}) return;

    // Uncached yazmada word daima data[31:0]'dadır (RTL sözleşmesi).
    wval       = t.wdata[31:0];
    tohost_val = wval;
    test_done  = 1;
    test_passed = (wval == 32'h1);

    if (test_passed)
      `uvm_info("SB", "*** tohost=1 : TEST PASS ***", UVM_LOW)
    else
      `uvm_error("SB", $sformatf(
          "*** tohost=0x%08h : TEST FAIL (kod=%0d, mcause=%0d) ***",
          wval, wval >> 1, wval >> 1))

    // Virtual sequence'lara "bitti" haberini olay havuzundan duyur.
    begin
      uvm_event ev = uvm_event_pool::get_global("lv_test_done");
      ev.trigger();
    end
  endfunction

  // Okuma yanıtını referans modelle karşılaştır.
  protected function void check_read_integrity(mem_txn t);
    bit [127:0] exp;
    if (!mem_cfg.en_rd_check) return;
    exp = t.uncached ? mem_cfg.model.read_uncached(t.addr)
                     : mem_cfg.model.read_line(t.addr);
    if (t.rdata !== exp) begin
      n_rd_mismatch++;
      `uvm_error("SB", $sformatf(
          "Okuma verisi uyusmazligi @0x%08h (%s):\n  beklenen=0x%032h\n  gozlenen=0x%032h",
          t.addr, t.uncached ? "UNC" : "CHD", exp, t.rdata))
    end
  endfunction

  // --------------------------------------------------------------------------
  // Commit gözlemi
  // --------------------------------------------------------------------------
  function void write_sb_commit(commit_item t);
    n_commits++;
    last_activity_cycle = cycle_cnt;
    if (trace_fd != 0)
      $fwrite(trace_fd, "%0t pc_incr=0x%08h x%0d <= 0x%08h\n",
              t.ts, t.pc_incr, t.rd_addr, t.rd_wdata);
  endfunction

  // --------------------------------------------------------------------------
  // Watchdog — çevrim sayacı + hareketsizlik tespiti
  // --------------------------------------------------------------------------
  task run_phase(uvm_phase phase);
    @(posedge vif.rst_n);
    forever begin
      @(posedge vif.clk);
      cycle_cnt++;
      if (!test_done &&
          (cycle_cnt - last_activity_cycle) > wd_commit_limit) begin
        `uvm_fatal("SB_WATCHDOG", $sformatf(
            "Cekirdek %0d cevrimdir ne commit etti ne bellek istegi uretti — kilitlenme! (son_hareket=%0d simdiki=%0d)",
            wd_commit_limit, last_activity_cycle, cycle_cnt))
      end
    end
  endtask

  // Faz bitmeye hazırlanırken son bir tutarlılık raporu şansı (ileri düzey:
  // phase_ready_to_end — objection'lar düşerken araya girme noktası).
  function void phase_ready_to_end(uvm_phase phase);
    if (phase.get_name() == "run" && !test_done)
      `uvm_warning("SB", "Run fazi tohost yazilmadan bitiyor (zaman asimi?)")
  endfunction

  // --------------------------------------------------------------------------
  // Nihai karar
  // --------------------------------------------------------------------------
  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    if (!test_done)
      `uvm_error("SB", "Test tohost'a hic yazmadan sonlandi")
    else if (!test_passed)
      `uvm_error("SB", $sformatf("Program FAIL bildirdi (tohost=0x%08h)",
                                 tohost_val))
    if (n_rd_mismatch != 0)
      `uvm_error("SB", $sformatf("%0d okuma verisi uyusmazligi", n_rd_mismatch))
  endfunction

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info("SB", $sformatf(
        "Ozet: okuma=%0d yazma=%0d commit=%0d uyusmazlik=%0d tohost=0x%08h (%s)",
        n_reads, n_writes, n_commits, n_rd_mismatch, tohost_val,
        !test_done ? "YAZILMADI" : (test_passed ? "PASS" : "FAIL")), UVM_LOW)
    if (trace_fd != 0) $fclose(trace_fd);
  endfunction

endclass : level_v_scoreboard
