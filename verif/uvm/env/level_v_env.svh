// ============================================================================
// Level RISC-V UVM — Ortam (Environment)
// ----------------------------------------------------------------------------
// Bileşen ağacı:
//
//   level_v_env
//   ├── mem_agent   (reaktif slave: monitor + sequencer + driver)
//   ├── irq_agent   (master: monitor + sequencer + driver)
//   ├── commit_mon  (bind edilen commit_if'ten pasif gözlem)
//   ├── scoreboard  (tohost + bütünlük + watchdog + trace)
//   ├── coverage    (mem/irq/commit covergroup'ları)
//   └── vsqr        (virtual sequencer — vseq eşgüdüm noktası)
//
// Analysis bağlantıları:
//   mem_agent.txn_ap    -> scoreboard.mem_imp, coverage.mem_imp
//   irq_agent.irq_ap    -> coverage.irq_imp
//   commit_mon.commit_ap-> scoreboard.commit_imp, coverage.commit_imp
//
// Konfigürasyon dağıtımı: test, level_v_env_cfg'yi env'e verir; env alt
// cfg'leri kendi çocuklarının görebileceği yollara yeniden yayınlar
// ("config dağıtım katmanı" deseni — çocuklar üst hiyerarşiyi bilmez).
// ============================================================================

class level_v_env extends uvm_env;

  `uvm_component_utils(level_v_env)

  level_v_env_cfg    cfg;
  mem_agent          mem_agt;
  irq_agent          irq_agt;
  commit_monitor     commit_mon;
  level_v_scoreboard scoreboard;
  level_v_coverage   coverage;
  level_v_vsequencer vsqr;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(level_v_env_cfg)::get(this, "", "env_cfg", cfg))
      `uvm_fatal("ENV", "level_v_env_cfg config_db'de yok — test kurmali")

    // Alt cfg'leri çocukların yollarına yayınla. "*" bu env'in altındaki
    // tüm bileşenleri kapsar (scoreboard'un mem_cfg alması dahil).
    uvm_config_db#(mem_agent_cfg)::set(this, "*", "mem_cfg", cfg.mem_cfg);
    uvm_config_db#(irq_agent_cfg)::set(this, "*", "irq_cfg", cfg.irq_cfg);

    mem_agt    = mem_agent::type_id::create("mem_agt", this);
    irq_agt    = irq_agent::type_id::create("irq_agt", this);
    commit_mon = commit_monitor::type_id::create("commit_mon", this);

    if (cfg.en_scoreboard)
      scoreboard = level_v_scoreboard::type_id::create("scoreboard", this);
    if (cfg.en_coverage)
      coverage = level_v_coverage::type_id::create("coverage", this);

    vsqr = level_v_vsequencer::type_id::create("vsqr", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    if (cfg.en_scoreboard) begin
      mem_agt.txn_ap.connect(scoreboard.mem_imp);
      commit_mon.commit_ap.connect(scoreboard.commit_imp);
      // Test, tohost'u cfg'de değiştirdiyse scoreboard'a yansıt.
      // Plusarg en yüksek önceliklidir: scoreboard build_phase'te okuduysa
      // cfg değeriyle EZİLMEZ.
      if (!scoreboard.tohost_from_plusarg)
        scoreboard.tohost_addr = cfg.tohost_addr;
    end

    if (cfg.en_coverage) begin
      mem_agt.txn_ap.connect(coverage.mem_imp);
      irq_agt.irq_ap.connect(coverage.irq_imp);
      commit_mon.commit_ap.connect(coverage.commit_imp);
    end

    // Virtual sequencer işaretçilerini bağla.
    vsqr.cfg     = cfg;
    vsqr.mem_sqr = (cfg.mem_cfg.is_active == UVM_ACTIVE) ? mem_agt.sequencer
                                                         : null;
    vsqr.irq_sqr = (cfg.irq_cfg.is_active == UVM_ACTIVE) ? irq_agt.sequencer
                                                         : null;
  endfunction

endclass : level_v_env
