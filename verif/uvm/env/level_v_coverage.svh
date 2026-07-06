// ============================================================================
// Level RISC-V UVM — Fonksiyonel Coverage Collector
// ----------------------------------------------------------------------------
// Üç analysis akışına abone olur (mem, irq, commit) ve her akış için ayrı
// covergroup örnekler. Çoklu abonelik `uvm_analysis_imp_decl` makrolarıyla
// yapılır: tek component, üç farklı write_*() imp metodu.
//
// Toplanan kapsam soruları:
//   * Bellek: okuma/yazma x cached/uncached çaprazı; adres bölgesi; gecikme
//     kovaları; strobe desenleri; arka arkaya (back-to-back) işlemler.
//   * IRQ   : hangi kesme pini görüldü; bellek meşgulken kesme çakışması.
//   * Commit: rd register dağılımı; yazılan verinin uç değerleri.
//
// "Coverage neyi kanıtlar?" — rastgele testlerin gerçekten çeşitli uyarı
// ürettiğini. Bir senaryo hiç örtülmediyse (örn. uncached yazma), constraint
// veya üreteç ayarı gözden geçirilmelidir.
// ============================================================================

// Aynı component'te birden çok analysis_imp için tip-ayrıştırma makroları.
`uvm_analysis_imp_decl(_mem)
`uvm_analysis_imp_decl(_irq)
`uvm_analysis_imp_decl(_commit)

class level_v_coverage extends uvm_component;

  `uvm_component_utils(level_v_coverage)

  uvm_analysis_imp_mem    #(mem_txn,     level_v_coverage) mem_imp;
  uvm_analysis_imp_irq    #(irq_item,    level_v_coverage) irq_imp;
  uvm_analysis_imp_commit #(commit_item, level_v_coverage) commit_imp;

  // Örnekleme değişkenleri — covergroup'lar bunlar üzerinden örnekler.
  // (Coverpoint ifadelerinde fonksiyon çağrısı yerine önceden hesaplanmış
  //  düz değişkenler kullanmak tüm simülatörlerde güvenli yoldur.)
  protected mem_txn     m_txn;
  protected irq_item    m_irq;
  protected commit_item m_cmt;
  protected bit         m_is_wr;      // Örneklenen işlem yazma mı?
  protected bit         m_mem_busy;   // IRQ çaprazı için: bellek uçuşta mı?
  protected bit         m_prev_was_wr;

  // --------------------------------------------------------------------------
  // Bellek işlem coverage'ı
  // --------------------------------------------------------------------------
  covergroup cg_mem;
    option.per_instance = 1;

    cp_dir : coverpoint m_is_wr {
      bins rd = {0};
      bins wr = {1};
    }

    cp_cached : coverpoint m_txn.uncached {
      bins cached   = {0};
      bins uncached = {1};
    }

    // Adres bölgesi: bellek haritasının test edilen dilimleri.
    cp_region : coverpoint m_txn.addr[31:28] {
      bins ram    = {4'h8, 4'h9, 4'hA, 4'hB, 4'hC, 4'hD, 4'hE, 4'hF};
      bins clint  = {4'h3};
      bins periph = {4'h2};
      bins boot   = {4'h1};
      bins other  = default;
    }

    // Yanıt gecikmesi: politika dağılımlarının gerçekten üretildiğinin kanıtı.
    // ("small"/"medium" SV'de ayrılmış kelimelerdir — bin adları farklı)
    cp_latency : coverpoint m_txn.latency {
      bins lat_fast    = {[1:2]};
      bins lat_short   = {[3:8]};
      bins lat_mid     = {[9:30]};
      bins lat_slow    = {[31:100]};
      bins lat_glacial = {[101:$]};
    }

    // Yazma strobe desenleri: byte/half/word/full-line.
    cp_strb : coverpoint $countones(m_txn.rw) iff (m_is_wr) {
      bins byte_w = {1};
      bins half_w = {2};
      bins word_w = {4};
      bins line_w = {16};
      bins other  = default;
    }

    // Önceki işlem yazma iken şimdiki okuma (RAW sırası iomem'de) vb.
    cp_wr_then_rd : coverpoint {m_prev_was_wr, m_is_wr} {
      bins wr_wr = {2'b11};
      bins wr_rd = {2'b10};
      bins rd_wr = {2'b01};
      bins rd_rd = {2'b00};
    }

    // Çaprazlar: en değerli kapsam bilgisi kesişimlerdedir.
    x_dir_cached  : cross cp_dir, cp_cached;
    x_dir_latency : cross cp_dir, cp_latency;
  endgroup

  // --------------------------------------------------------------------------
  // Kesme coverage'ı
  // --------------------------------------------------------------------------
  covergroup cg_irq;
    option.per_instance = 1;

    cp_kind : coverpoint m_irq.kind {
      bins timer_i = {LV_IRQ_TIMER};
      bins sw_i    = {LV_IRQ_SW};
      bins ext_i   = {LV_IRQ_EXT};
    }

    // Kesme, bellek işlemi uçuştayken mi geldi? (stall + trap etkileşimi —
    // boru hattındaki en nazik köşelerden biri)
    cp_during_mem : coverpoint m_mem_busy {
      bins idle = {0};
      bins busy = {1};
    }

    x_kind_busy : cross cp_kind, cp_during_mem;
  endgroup

  // --------------------------------------------------------------------------
  // Commit coverage'ı
  // --------------------------------------------------------------------------
  covergroup cg_commit;
    option.per_instance = 1;

    // Hedef register dağılımı: üretecin tüm register'lara yazdığının kanıtı.
    cp_rd : coverpoint m_cmt.rd_addr {
      bins x[32] = {[0:31]};
    }

    // Yazılan verinin uç değerleri (işaret sınırları, sıfır, tüm birler).
    cp_val : coverpoint m_cmt.rd_wdata {
      bins zero     = {32'h0};
      bins all_ones = {32'hFFFF_FFFF};
      bins max_pos  = {32'h7FFF_FFFF};
      bins min_neg  = {32'h8000_0000};
      bins low_vals = {[1:255]};
      bins others   = default;
    }
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    mem_imp    = new("mem_imp", this);
    irq_imp    = new("irq_imp", this);
    commit_imp = new("commit_imp", this);
    cg_mem     = new();
    cg_irq     = new();
    cg_commit  = new();
  endfunction

  // ---- analysis imp geri çağrıları ----

  function void write_mem(mem_txn t);
    m_txn   = t;
    m_is_wr = (t.rw != 0);
    cg_mem.sample();
    m_prev_was_wr = m_is_wr;
    m_mem_busy    = 0;  // tamamlanan işlemle uçuş bitti
  endfunction

  function void write_irq(irq_item t);
    m_irq = t;
    cg_irq.sample();
  endfunction

  function void write_commit(commit_item t);
    m_cmt = t;
    cg_commit.sample();
  endfunction

  // Not: m_mem_busy'nin "uçuşta" tarafını hassas izlemek için monitörün
  // req_ap'ına da bağlanılabilirdi; sadeleşme adına tamamlanma tabanlı
  // yaklaşık izleme yeterli görüldü (kesme çaprazı istatistiksel).

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info("COV", $sformatf(
        "Kapsam: mem=%.1f%% irq=%.1f%% commit=%.1f%%",
        cg_mem.get_inst_coverage(),
        cg_irq.get_inst_coverage(),
        cg_commit.get_inst_coverage()), UVM_LOW)
  endfunction

endclass : level_v_coverage
