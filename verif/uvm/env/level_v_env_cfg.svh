// ============================================================================
// Level RISC-V UVM — Ortam (Env) Konfigürasyon Nesnesi
// ----------------------------------------------------------------------------
// Hiyerarşik konfigürasyon deseni: env cfg, alt-agent cfg'lerini İÇERİR.
// Test yalnızca bu nesneyi kurup config_db'ye koyar; env, alt cfg'leri
// kendi altına dağıtır. Böylece test-env arayüzü tek nesneye iner ve
// yeni knob eklemek hiçbir imza değiştirmez.
// ============================================================================

class level_v_env_cfg extends uvm_object;

  // Alt agent konfigürasyonları
  mem_agent_cfg mem_cfg;
  irq_agent_cfg irq_cfg;

  // Ortam seviyesi anahtarlar
  bit en_scoreboard = 1;
  bit en_coverage   = 1;

  // tohost adresi (scoreboard'a ve program üretecine tek yerden)
  bit [31:0] tohost_addr = LV_TOHOST_DEFAULT;

  `uvm_object_utils_begin(level_v_env_cfg)
    `uvm_field_object(mem_cfg, UVM_DEFAULT)
    `uvm_field_object(irq_cfg, UVM_DEFAULT)
    `uvm_field_int(en_scoreboard, UVM_DEFAULT)
    `uvm_field_int(en_coverage, UVM_DEFAULT)
    `uvm_field_int(tohost_addr, UVM_DEFAULT | UVM_HEX)
  `uvm_object_utils_end

  function new(string name = "level_v_env_cfg");
    super.new(name);
    // Alt cfg'ler factory'den: testler tür değiştirebilsin (override).
    mem_cfg = mem_agent_cfg::type_id::create("mem_cfg");
    irq_cfg = irq_agent_cfg::type_id::create("irq_cfg");
  endfunction

endclass : level_v_env_cfg
