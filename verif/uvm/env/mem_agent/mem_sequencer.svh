// ============================================================================
// Level RISC-V UVM — Bellek Sequencer'ı (Reaktif Slave Deseni)
// ----------------------------------------------------------------------------
// Klasik master sequencer'dan farkı: içinde bir "istek FIFO'su" taşır.
// Monitör, DUT'tan gelen HAM istekleri analysis port'u ile bu FIFO'ya yazar;
// responder sequence `p_sequencer.req_fifo.get(...)` ile istekleri çeker,
// bellek modelinden yanıtı hesaplar ve rastgele gecikmeli mem_rsp_item'ı
// driver'a gönderir.
//
// Bu, ileri düzey UVM'in standart "reactive slave sequence" mimarisidir:
//   DUT isteği -> monitor -> [req_fifo] -> slave sequence -> driver -> DUT
// Yanıt İÇERİĞİ ve ZAMANLAMASI tamamen sequence katmanında kalır; driver
// yalnızca pin seviyesi sürüş yapar. Böylece "bozuk yanıt", "aşırı gecikme"
// gibi senaryolar sequence değiştirerek (veya factory override ile) elde
// edilir, driver'a dokunulmaz.
// ============================================================================

class mem_sequencer extends uvm_sequencer #(mem_rsp_item);

  `uvm_component_utils(mem_sequencer)

  // Monitörden gelen ham istekler. Analysis-imp tarafı FIFO'nun kendisinde:
  // agent connect_phase'de monitörün req_ap'ını buraya bağlar.
  uvm_tlm_analysis_fifo #(mem_txn) req_fifo;

  // Agent cfg'ye sequence'ların p_sequencer üzerinden kolay erişimi için.
  mem_agent_cfg cfg;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  // Çocuk component'ler build_phase'te yaratılır. Örnek adı BİLEREK
  // "iomem_req_fifo": uvm_sequencer_param_base kendi içinde "req_fifo"
  // adında dahili bir çocuk (m_req_fifo) yaratır; aynı adı kullanmak
  // CLDEXT (duplicate child) ölümcül hatasına yol açar.
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    req_fifo = new("iomem_req_fifo", this);
  endfunction

endclass : mem_sequencer
