// ============================================================================
// Level RISC-V UVM — Virtual Sequence Kütüphanesi
// ----------------------------------------------------------------------------
// Senaryo katmanı. Her vseq, virtual sequencer üzerinden ortamdaki tüm
// aktörleri koordine eder:
//
//   * Bellek responder'ını başlatır (o olmadan çekirdek ilk fetch'te takılır),
//   * Programı hazırlar (rastgele üretim ya da +firmware hex yüklemesi),
//   * Reset'i tb_top'a bıraktığı için yalnızca stimulus'la ilgilenir,
//   * scoreboard'un tetiklediği "lv_test_done" olayını bekleyerek biter.
//
// Objection yönetimi bilinçli olarak TESTTE değil BURADADIR: senaryonun ne
// zaman bittiğini en iyi senaryo bilir (uvm_event ile). Test yalnızca vseq'i
// başlatır ve zaman aşımı sigortasını kurar.
// ============================================================================

// ----------------------------------------------------------------------------
// Taban vseq: responder yaşam döngüsü + bitiş olayı bekleme yardımcıları.
// ----------------------------------------------------------------------------
class level_v_base_vseq extends uvm_sequence;

  `uvm_object_utils(level_v_base_vseq)
  `uvm_declare_p_sequencer(level_v_vsequencer)

  // Bellek responder'ı arka planda sonsuza dek koşar; handle'ı saklanır.
  protected mem_responder_seq m_responder;

  function new(string name = "level_v_base_vseq");
    super.new(name);
  endfunction

  // Responder'ı arka planda başlat. Factory üzerinden yaratıldığı için
  // set_type_override ile (örn. mem_heavy_backpressure_seq) değiştirilebilir.
  protected task start_mem_responder();
    if (p_sequencer.mem_sqr == null)
      `uvm_fatal("VSEQ", "mem sequencer yok (agent pasif mi?)")
    m_responder = mem_responder_seq::type_id::create("responder");
    fork
      m_responder.start(p_sequencer.mem_sqr);
    join_none
  endtask

  // Scoreboard'un tohost tespitini olay havuzundan bekle.
  // Sigorta: max_cycles sonunda hâlâ olay yoksa zaman aşımı raporla —
  // (watchdog büyük olasılıkla daha önce patlar; bu ikinci hattır.)
  protected task wait_test_done(int unsigned max_us = 200_000);
    uvm_event ev = uvm_event_pool::get_global("lv_test_done");
    fork begin
      fork
        ev.wait_trigger();
        begin
          #(max_us * 1us);
          `uvm_error("VSEQ", $sformatf(
              "Zaman asimi: %0d us icinde tohost yazilmadi", max_us))
        end
      join_any
      disable fork;
    end join
  endtask

  virtual task body();
    `uvm_fatal("VSEQ", "Taban vseq dogrudan calistirilamaz")
  endtask

endclass : level_v_base_vseq


// ----------------------------------------------------------------------------
// Rastgele program vseq'i: üret + yükle + koş + bitişi bekle.
// Üretecin knob'ları bu vseq'in rand alanlarıdır -> test "randomize with"
// ile senaryoyu şekillendirir (constraint katmanlama).
// ----------------------------------------------------------------------------
class random_program_vseq extends level_v_base_vseq;

  `uvm_object_utils(random_program_vseq)

  rand int unsigned n_instrs;
  rand bit          en_compressed;
       bit          irq_mode = 0;   // türev vseq'ler açar

  // rand OLMAYAN sınır knob'ları: testler make_vseq içinde bunları ayarlar,
  // randomize daha sonra (taban testin run_phase'inde) çağrılır. Böylece
  // "randomize'ı kim, ne zaman çağırıyor" tek yerde kalır.
  int unsigned min_instrs = 100;
  int unsigned max_instrs = 2000;

  constraint c_defaults {
    n_instrs inside {[min_instrs:max_instrs]};
    en_compressed dist { 1 :/ 70, 0 :/ 30 };
  }

  function new(string name = "random_program_vseq");
    super.new(name);
  endfunction

  virtual task body();
    rv32_program_gen gen;

    // 1) Bellek "canlanmadan" önce programı modele backdoor yükle.
    gen = rv32_program_gen::type_id::create("gen");
    if (!gen.randomize() with {
          n_instrs      == local::n_instrs;
          en_compressed == local::en_compressed;
        })
      `uvm_fatal("VSEQ", "Program ureteci randomize edilemedi")
    gen.irq_mode = irq_mode;
    gen.tohost   = p_sequencer.cfg.tohost_addr;
    void'(gen.build(p_sequencer.cfg.mem_cfg.model));

    // 2) Bellek responder'ını başlat — çekirdek ilk fetch'ini alabilsin.
    start_mem_responder();

    // 3) Program kendini sonlandırana kadar bekle.
    wait_test_done();
  endtask

endclass : random_program_vseq


// ----------------------------------------------------------------------------
// Kesme stres vseq'i: irq_mode'lu rastgele program + paralel kesme fırtınası.
// İki uyarı kaynağının fork ile eşzamanlı koşturulması, virtual sequence
// katmanının varlık sebebidir.
// ----------------------------------------------------------------------------
class irq_stress_vseq extends random_program_vseq;

  `uvm_object_utils(irq_stress_vseq)

  rand int unsigned n_irq_pulses;

  constraint c_irq { n_irq_pulses inside {[20:500]}; }

  function new(string name = "irq_stress_vseq");
    super.new(name);
    irq_mode = 1;  // program, kesmeleri etkinleştirip handler'da saysın
  endfunction

  virtual task body();
    irq_storm_seq storm;

    if (p_sequencer.irq_sqr == null)
      `uvm_fatal("VSEQ", "irq sequencer yok (agent pasif mi?)")

    // Kesme fırtınası arka planda (join_none): erken biterse sorun değil,
    // program yine kendi başına sonlanır. Ana akış (program yükle + bitişi
    // bekle) HER ZAMAN tamamlanmalı — bu yüzden join_any KULLANILMAZ;
    // aksi halde fırtına önce bitince test-bitti beklemesi öldürülürdü.
    fork
      begin
        storm = irq_storm_seq::type_id::create("storm");
        if (!storm.randomize() with { n_pulses == local::n_irq_pulses; })
          `uvm_fatal("VSEQ", "irq_storm_seq randomize edilemedi")
        storm.start(p_sequencer.irq_sqr);
      end
    join_none

    // Ana akış: program üret/yükle/koş (üst sınıfın gövdesi).
    super.body();
  endtask

endclass : irq_stress_vseq


// ----------------------------------------------------------------------------
// Harici (hex) program vseq'i: riscv-dv / riscv-tests üretimi imajları koşar.
//   +firmware=<yol>.hex  (zorunlu)
//   +tohost_addr=0x...   (imajin link.ld'sindeki tohost adresi)
// Mevcut make akışlarıyla köprü: riscv-dv'nin ürettiği .hex buradan girer.
// ----------------------------------------------------------------------------
class hex_program_vseq extends level_v_base_vseq;

  `uvm_object_utils(hex_program_vseq)

  function new(string name = "hex_program_vseq");
    super.new(name);
  endfunction

  virtual task body();
    string fw;
    if (!$value$plusargs("firmware=%s", fw))
      `uvm_fatal("VSEQ", "+firmware=<dosya.hex> plusarg'i gerekli")

    p_sequencer.cfg.mem_cfg.model.load_hex_file(fw, LV_RESET_VECTOR);

    start_mem_responder();
    wait_test_done(900_000);  // harici imajlar daha uzun koşabilir
                              // (küresel 1s faz zaman aşımının hemen altında)
  endtask

endclass : hex_program_vseq
