// ============================================================================
// Level RISC-V UVM — Test Kütüphanesi
// ----------------------------------------------------------------------------
// Testler İNCE tutulur: konfigürasyon kurar, (gerekirse) factory override
// yapar, vseq'i başlatır. Senaryo bilgisi vseq'te, yapı bilgisi env'de,
// ayar bilgisi cfg'dedir — test yalnızca bunları birbirine bağlar.
//
//   +UVM_TESTNAME=level_v_random_test         (varsayılan duman testi)
//   +UVM_TESTNAME=level_v_random_stress_test  (uzun, rastgele gecikmeli)
//   +UVM_TESTNAME=level_v_irq_stress_test     (kesme fırtınası)
//   +UVM_TESTNAME=level_v_backpressure_test   (ağır bellek gecikmesi,
//                                              factory override + callback)
//   +UVM_TESTNAME=level_v_hex_test            (+firmware=... imaj koşucu)
//
// Ek plusarg'lar: +n_instrs=<N>  +tohost_addr=0x...  +wd_limit=<N>
//                 +lv_trace=<dosya>  +iomem_assert_off
// ============================================================================

// ----------------------------------------------------------------------------
// Taban test: ortak kurulum.
// ----------------------------------------------------------------------------
class level_v_base_test extends uvm_test;

  `uvm_component_utils(level_v_base_test)

  level_v_env     env;
  level_v_env_cfg cfg;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Konfigürasyon nesnesini kur; türev testler configure_env ile ezer.
    cfg = level_v_env_cfg::type_id::create("cfg");
    configure_env(cfg);
    uvm_config_db#(level_v_env_cfg)::set(this, "env", "env_cfg", cfg);

    env = level_v_env::type_id::create("env", this);

    // Küresel sigorta: hiçbir şey ilerlemezse UVM faz zaman aşımı.
    // (vseq'in kendi zaman aşımı ve scoreboard watchdog'u bundan önce
    //  devreye girer; bu üçüncü ve son hattır)
    uvm_root::get().set_timeout(1s, 1);
  endfunction

  // Türev testlerin tek özelleştirme noktası (template method deseni).
  virtual function void configure_env(level_v_env_cfg c);
    c.mem_cfg.lat_policy = LV_LAT_SMALL;
  endfunction

  // Vseq seçimi de override edilebilir bir fabrika metodu.
  virtual function level_v_base_vseq make_vseq();
    return random_program_vseq::type_id::create("vseq");
  endfunction

  task run_phase(uvm_phase phase);
    level_v_base_vseq vseq;

    // Objection burada kaldırılır; senaryonun bitişini vseq bilir
    // (scoreboard'un lv_test_done olayını bekler ve döner).
    phase.raise_objection(this, "vseq calisiyor");
    // Drain time: son tohost yazmasından sonra boru hattının boşalması ve
    // son analysis işlemlerinin akması için küçük bir kuyruk süresi.
    // (UVM 1.2 erişimcisi get_objection(); phase_done alanı 1.2'de korumalı)
    phase.get_objection().set_drain_time(this, 1us);

    vseq = make_vseq();
    if (!vseq.randomize())
      `uvm_fatal("TEST", "vseq randomize edilemedi")
    apply_plusarg_overrides(vseq);
    vseq.start(env.vsqr);

    phase.drop_objection(this, "vseq bitti");
  endtask

  // +n_instrs plusarg'i ile hızlı deneme: randomize SONRASI bilinçli ezme.
  protected function void apply_plusarg_overrides(level_v_base_vseq vseq);
    int unsigned n;
    random_program_vseq rp;
    if ($value$plusargs("n_instrs=%d", n) && $cast(rp, vseq)) begin
      rp.n_instrs = n;
      `uvm_info("TEST", $sformatf("n_instrs plusarg ile %0d yapildi", n),
                UVM_LOW)
    end
  endfunction

  // Kapanışta factory ve topolojiyi raporla (hata ayıklamada paha biçilmez).
  function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    if (uvm_report_enabled(UVM_HIGH)) begin
      uvm_root::get().print_topology();
      uvm_factory::get().print();
    end
  endfunction

endclass : level_v_base_test


// ----------------------------------------------------------------------------
// Duman/regresyon testi: orta boy rastgele program, gerçekçi bellek.
// ----------------------------------------------------------------------------
class level_v_random_test extends level_v_base_test;

  `uvm_component_utils(level_v_random_test)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  // Taban ayarlar yeterli — sınıf, isimli bir regresyon girdisi olarak var.

endclass : level_v_random_test


// ----------------------------------------------------------------------------
// Uzun stres: büyük program + düz-rastgele bellek gecikmesi.
// ----------------------------------------------------------------------------
class level_v_random_stress_test extends level_v_base_test;

  `uvm_component_utils(level_v_random_stress_test)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void configure_env(level_v_env_cfg c);
    c.mem_cfg.lat_policy = LV_LAT_RANDOM;
    c.mem_cfg.lat_min    = 1;
    c.mem_cfg.lat_max    = 40;
  endfunction

  virtual function level_v_base_vseq make_vseq();
    random_program_vseq v = random_program_vseq::type_id::create("vseq");
    // Constraint sınırlarını daralt; randomize'ı taban test çağırır
    // (make_vseq -> randomize sıralaması level_v_base_test.run_phase'te).
    v.min_instrs = 1500;
    v.max_instrs = 2000;
    return v;
  endfunction

endclass : level_v_random_stress_test


// ----------------------------------------------------------------------------
// Kesme fırtınası testi.
// ----------------------------------------------------------------------------
class level_v_irq_stress_test extends level_v_base_test;

  `uvm_component_utils(level_v_irq_stress_test)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void configure_env(level_v_env_cfg c);
    c.mem_cfg.lat_policy = LV_LAT_BURSTY;  // stall + kesme çakışmaları
  endfunction

  virtual function level_v_base_vseq make_vseq();
    return irq_stress_vseq::type_id::create("vseq");
  endfunction

endclass : level_v_irq_stress_test


// ----------------------------------------------------------------------------
// Backpressure testi — İKİ ileri düzey tekniğin tanıtımı:
//   1) Factory type override: responder sequence, testin tek satırıyla
//      mem_heavy_backpressure_seq'e dönüşür; env/vseq kodu değişmez.
//   2) uvm_callback: driver'a kaydedilen callback, her 64. yanıta ekstra
//      gecikme ekleyerek "arada takılan bellek" profili üretir.
// ----------------------------------------------------------------------------

// Callback örneği: periyodik ekstra gecikme.
class mem_extra_delay_cb extends mem_driver_cbs;

  `uvm_object_utils(mem_extra_delay_cb)

  int unsigned every_n  = 64;
  int unsigned extra    = 300;
  protected int unsigned cnt;

  function new(string name = "mem_extra_delay_cb");
    super.new(name);
  endfunction

  virtual task pre_response(mem_driver drv, mem_rsp_item item);
    cnt++;
    if (cnt % every_n == 0) begin
      item.latency += extra;
      `uvm_info("MEM_CB", $sformatf(
          "%0d. yanita +%0d cevrim eklendi (toplam %0d)",
          cnt, extra, item.latency), UVM_HIGH)
    end
  endtask

endclass : mem_extra_delay_cb


class level_v_backpressure_test extends level_v_base_test;

  `uvm_component_utils(level_v_backpressure_test)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    // 1) Factory override — build'den ÖNCE yapılmalı ki create'ler türevi
    //    üretsin. (Responder vseq içinde create edildiği için run'da da işe
    //    yarardı ama kural olarak erken yapmak güvenlidir.)
    mem_responder_seq::type_id::set_type_override(
        mem_heavy_backpressure_seq::get_type());
    super.build_phase(phase);
  endfunction

  function void end_of_elaboration_phase(uvm_phase phase);
    mem_extra_delay_cb cb;
    super.end_of_elaboration_phase(phase);
    // 2) Callback kaydı — driver artık var, kancaya takılabilir.
    cb = mem_extra_delay_cb::type_id::create("extra_delay_cb");
    uvm_callbacks#(mem_driver, mem_driver_cbs)::add(env.mem_agt.driver, cb);
  endfunction

  virtual function void configure_env(level_v_env_cfg c);
    c.mem_cfg.lat_policy = LV_LAT_HEAVY;  // override zaten dayatir; belgeleyici
  endfunction

endclass : level_v_backpressure_test


// ----------------------------------------------------------------------------
// Harici hex imaj koşucu (riscv-dv / riscv-tests köprüsü).
// ----------------------------------------------------------------------------
class level_v_hex_test extends level_v_base_test;

  `uvm_component_utils(level_v_hex_test)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function level_v_base_vseq make_vseq();
    return hex_program_vseq::type_id::create("vseq");
  endfunction

endclass : level_v_hex_test
