// ============================================================================
// Level RISC-V UVM — Bellek Agent'ı (Reaktif Slave Agent)
// ----------------------------------------------------------------------------
// Standart UVM agent iskeleti; cfg.is_active'e göre iki kılıkta çalışır:
//
//   UVM_ACTIVE : monitor + sequencer + driver. Ortam, çekirdeğin belleği
//                olarak davranır (responder sequence env'den başlatılır).
//   UVM_PASSIVE: yalnızca monitor. Örn. DUT'un gerçek SoC sarmalayıcı ile
//                koşulduğu bir üst-seviye ortamda protokol izleme/coverage
//                için yeniden kullanılabilir.
//
// Bağlantı özeti (connect_phase):
//   monitor.req_ap  -> sequencer.req_fifo (reaktif slave beslemesi)
//   monitor.txn_ap  -> dışarı (env: scoreboard + coverage buradan bağlanır)
//   driver.seq_item_port -> sequencer.seq_item_export
// ============================================================================

class mem_agent extends uvm_agent;

  `uvm_component_utils(mem_agent)

  mem_agent_cfg cfg;
  mem_monitor   monitor;
  mem_sequencer sequencer;
  mem_driver    driver;

  // Env'in scoreboard/coverage bağlaması için dışa açılan port (pass-through).
  uvm_analysis_port #(mem_txn) txn_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(mem_agent_cfg)::get(this, "", "mem_cfg", cfg))
      `uvm_fatal("MEM_AGT", "mem_agent_cfg config_db'de yok")

    txn_ap  = new("txn_ap", this);
    monitor = mem_monitor::type_id::create("monitor", this);

    if (cfg.is_active == UVM_ACTIVE) begin
      sequencer     = mem_sequencer::type_id::create("sequencer", this);
      sequencer.cfg = cfg;  // p_sequencer.cfg erişimi için doğrudan atama
      driver        = mem_driver::type_id::create("driver", this);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // Tamamlanan işlemleri agent sınırından dışarı aktar.
    monitor.txn_ap.connect(txn_ap);

    if (cfg.is_active == UVM_ACTIVE) begin
      // Reaktif besleme: ham istekler sequencer'daki FIFO'ya akar.
      monitor.req_ap.connect(sequencer.req_fifo.analysis_export);
      driver.seq_item_port.connect(sequencer.seq_item_export);
    end
  endfunction

endclass : mem_agent
