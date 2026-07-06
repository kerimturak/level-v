// ============================================================================
// Level RISC-V UVM — Virtual Sequencer
// ----------------------------------------------------------------------------
// Hiçbir item türü sürmez ("virtual"); yalnızca alt sequencer'lara ve
// paylaşılan kaynaklara (cfg) TİPLİ işaretçiler taşır. Virtual sequence'lar
// `uvm_declare_p_sequencer(level_v_vsequencer)` ile bu işaretçiler üzerinden
// hem bellek responder'ını hem kesme üretimini TEK senaryoda koordine eder —
// çok-arayüzlü ortamların standart eşgüdüm katmanı.
// ============================================================================

class level_v_vsequencer extends uvm_sequencer;

  `uvm_component_utils(level_v_vsequencer)

  // Alt sequencer işaretçileri (env connect_phase'de doldurur)
  mem_sequencer  mem_sqr;
  irq_sequencer  irq_sqr;

  // Paylaşılan konfigürasyon — vseq'ler program üretecini mem_cfg.model'e
  // yazdırmak ve tohost adresini öğrenmek için kullanır.
  level_v_env_cfg cfg;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

endclass : level_v_vsequencer
