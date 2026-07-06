// ============================================================================
// Level RISC-V UVM — Bellek Agent Konfigürasyon Nesnesi
// ----------------------------------------------------------------------------
// "Configuration object" deseni: agent'ın tüm ayar düğmeleri (knob) tek bir
// uvm_object'te toplanır ve uvm_config_db ile hiyerarşiye dağıtılır.
// Böylece testler, agent'ın içine dokunmadan davranışını değiştirir.
//
// Ayrıca paylaşılan mem_model referansı buradadır: driver'a gerek yok ama
// responder sequence, scoreboard ve program üreteci AYNI modeli kullanır.
// ============================================================================

class mem_agent_cfg extends uvm_object;

  // ---- Agent yapısı ----
  uvm_active_passive_enum is_active = UVM_ACTIVE;  // pasif -> sadece monitör

  // ---- Zamanlama / gecikme politikası ----
  // Responder sequence'ın yanıt gecikmesi constraint'lerini seçer.
  lv_lat_policy_e lat_policy = LV_LAT_SMALL;

  // Politika sınırlarının ince ayarı (LV_LAT_RANDOM/HEAVY için)
  int unsigned lat_min = 1;
  int unsigned lat_max = 20;

  // ---- Paylaşılan bellek modeli ----
  mem_model model;

  // ---- Kontrol ----
  bit en_cov      = 1;  // Agent-içi fonksiyonel coverage topla
  bit en_rd_check = 1;  // Scoreboard okuma-verisi bütünlük kontrolü

  `uvm_object_utils_begin(mem_agent_cfg)
    `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_DEFAULT)
    `uvm_field_enum(lv_lat_policy_e, lat_policy, UVM_DEFAULT)
    `uvm_field_int(lat_min, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(lat_max, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(en_cov, UVM_DEFAULT)
    `uvm_field_int(en_rd_check, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "mem_agent_cfg");
    super.new(name);
    // Model burada yaratılır; isteyen test factory override ile
    // farklı bir mem_model türevi enjekte edebilir.
    model = mem_model::type_id::create("model");
  endfunction

endclass : mem_agent_cfg
