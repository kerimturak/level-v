// ============================================================================
// Level RISC-V UVM — Kesme (IRQ) Agent'ı: item + cfg + driver + monitor +
//                     sequencer + agent + sequence kütüphanesi
// ----------------------------------------------------------------------------
// Küçük ama tam teşekküllü bir MASTER agent. Çekirdeğin 3 seviye-duyarlı
// kesme pinini (timer/sw/ext) rastgeleleştirilmiş darbelerle sürer.
//
// Kesmelerin anlamlı olabilmesi için koşan programın mstatus.MIE + mie
// bitlerini açmış ve mtvec'e "interrupt ise say ve mret yap" diyen bir
// handler kurmuş olması gerekir — rv32_program_gen'in irq_mode=1 çıktısı
// tam bunu üretir (bkz. prog_gen/rv32_program_gen.svh).
//
// Dosya, agent küçük olduğu için tek parça tutuldu; her sınıf yine de
// bağımsız ve factory üzerinden override edilebilir durumda.
// ============================================================================

// ----------------------------------------------------------------------------
// Sequence item: tek bir kesme darbesinin tam tarifi.
// ----------------------------------------------------------------------------
class irq_item extends uvm_sequence_item;

  rand lv_irq_kind_e kind;         // Hangi pin?
  rand int unsigned  pre_delay;    // Darbeden önce beklenecek çevrim
  rand int unsigned  pulse_len;    // Pinin yüksek tutulacağı çevrim sayısı

  `uvm_object_utils_begin(irq_item)
    `uvm_field_enum(lv_irq_kind_e, kind, UVM_DEFAULT)
    `uvm_field_int(pre_delay, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(pulse_len, UVM_DEFAULT | UVM_DEC)
  `uvm_object_utils_end

  // Varsayılan dağılımlar: kısa aralıklarla, handler'ın pin düşmeden
  // birden çok kez tetiklenebileceği kadar uzun darbeler.
  constraint c_delay { pre_delay inside {[0:400]}; }
  constraint c_pulse { pulse_len inside {[2:50]}; }

  function new(string name = "irq_item");
    super.new(name);
  endfunction

endclass : irq_item


// ----------------------------------------------------------------------------
// Konfigürasyon nesnesi
// ----------------------------------------------------------------------------
class irq_agent_cfg extends uvm_object;

  uvm_active_passive_enum is_active = UVM_ACTIVE;
  bit en_cov = 1;

  `uvm_object_utils_begin(irq_agent_cfg)
    `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_DEFAULT)
    `uvm_field_int(en_cov, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "irq_agent_cfg");
    super.new(name);
  endfunction

endclass : irq_agent_cfg


// ----------------------------------------------------------------------------
// Sequencer: özelleşme gerekmediği için typedef yeterli.
// ----------------------------------------------------------------------------
typedef uvm_sequencer #(irq_item) irq_sequencer;


// ----------------------------------------------------------------------------
// Driver: darbe tarifini pin dalgaformuna çevirir.
// Pinler bağımsızdır; aynı anda birden çok kesme örtüşebilsin diye her item
// kendi fork'unda sürülür (non-blocking sürüş) — "örtüşen kesmeler"
// senaryosu böylece sequence'ta hiçbir özel çaba gerektirmez.
// ----------------------------------------------------------------------------
class irq_driver extends uvm_driver #(irq_item);

  `uvm_component_utils(irq_driver)

  virtual irq_if vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual irq_if)::get(this, "", "irq_vif", vif))
      `uvm_fatal("IRQ_DRV", "irq_if sanal arayuzu config_db'de yok")
  endfunction

  // Tek pini süren yardımcı: pre_delay bekle, pulse_len boyunca yüksek tut.
  protected task drive_pulse(irq_item it);
    repeat (it.pre_delay) @(vif.drv_cb);
    case (it.kind)
      LV_IRQ_TIMER: vif.drv_cb.timer_irq <= 1'b1;
      LV_IRQ_SW:    vif.drv_cb.sw_irq    <= 1'b1;
      LV_IRQ_EXT:   vif.drv_cb.ext_irq   <= 1'b1;
    endcase
    repeat (it.pulse_len) @(vif.drv_cb);
    case (it.kind)
      LV_IRQ_TIMER: vif.drv_cb.timer_irq <= 1'b0;
      LV_IRQ_SW:    vif.drv_cb.sw_irq    <= 1'b0;
      LV_IRQ_EXT:   vif.drv_cb.ext_irq   <= 1'b0;
    endcase
  endtask

  task run_phase(uvm_phase phase);
    irq_item it;

    vif.drv_cb.timer_irq <= 1'b0;
    vif.drv_cb.sw_irq    <= 1'b0;
    vif.drv_cb.ext_irq   <= 1'b0;
    @(posedge vif.rst_n);

    forever begin
      seq_item_port.get_next_item(it);
      // İtemi hemen tamamlanmış say ve darbeyi arka planda sür:
      // sequence bir sonraki itemi üretebilir -> farklı pinlerde
      // örtüşen kesme darbeleri doğal olarak oluşur.
      fork
        automatic irq_item it_l = it;
        drive_pulse(it_l);
      join_none
      seq_item_port.item_done();
    end
  endtask

endclass : irq_driver


// ----------------------------------------------------------------------------
// Monitor: pin kenarlarını gözler, coverage collector'a yayınlar.
// ----------------------------------------------------------------------------
class irq_monitor extends uvm_component;

  `uvm_component_utils(irq_monitor)

  virtual irq_if vif;
  uvm_analysis_port #(irq_item) irq_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    irq_ap = new("irq_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual irq_if)::get(this, "", "irq_vif", vif))
      `uvm_fatal("IRQ_MON", "irq_if sanal arayuzu config_db'de yok")
  endfunction

  task run_phase(uvm_phase phase);
    logic [2:0] prev = '0, cur;
    @(posedge vif.rst_n);
    forever begin
      @(vif.mon_cb);
      cur = {vif.mon_cb.ext_irq, vif.mon_cb.sw_irq, vif.mon_cb.timer_irq};
      // Her yükselen kenar için bir gözlem itemi yayınla.
      for (int k = 0; k < 3; k++) begin
        if (cur[k] && !prev[k]) begin
          irq_item it = irq_item::type_id::create("irq_obs");
          it.kind = lv_irq_kind_e'(k);
          `uvm_info("IRQ_MON", $sformatf("Kesme yukselen kenar: %s",
                                         it.kind.name()), UVM_HIGH)
          irq_ap.write(it);
        end
      end
      prev = cur;
    end
  endtask

endclass : irq_monitor


// ----------------------------------------------------------------------------
// Agent
// ----------------------------------------------------------------------------
class irq_agent extends uvm_agent;

  `uvm_component_utils(irq_agent)

  irq_agent_cfg cfg;
  irq_driver    driver;
  irq_monitor   monitor;
  irq_sequencer sequencer;

  uvm_analysis_port #(irq_item) irq_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(irq_agent_cfg)::get(this, "", "irq_cfg", cfg))
      `uvm_fatal("IRQ_AGT", "irq_agent_cfg config_db'de yok")

    irq_ap  = new("irq_ap", this);
    monitor = irq_monitor::type_id::create("monitor", this);
    if (cfg.is_active == UVM_ACTIVE) begin
      driver    = irq_driver::type_id::create("driver", this);
      sequencer = irq_sequencer::type_id::create("sequencer", this);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    monitor.irq_ap.connect(irq_ap);
    if (cfg.is_active == UVM_ACTIVE)
      driver.seq_item_port.connect(sequencer.seq_item_export);
  endfunction

endclass : irq_agent


// ----------------------------------------------------------------------------
// Sequence kütüphanesi
// ----------------------------------------------------------------------------
// irq_quiet_seq: hiç kesme üretmez (pasif koşular için açık niyet beyanı).
class irq_quiet_seq extends uvm_sequence #(irq_item);
  `uvm_object_utils(irq_quiet_seq)
  function new(string name = "irq_quiet_seq");
    super.new(name);
  endfunction
  virtual task body();
    // bilerek boş
  endtask
endclass : irq_quiet_seq

// irq_storm_seq: n_pulses adet rastgele kesme darbesi. Yoğunluk, item
// constraint'lerini "randomize with" ile ezerek ayarlanır — sequence'tan
// constraint katmanlama (in-line constraint) örneği.
class irq_storm_seq extends uvm_sequence #(irq_item);

  `uvm_object_utils(irq_storm_seq)

  rand int unsigned n_pulses     = 50;
  rand int unsigned max_gap      = 300;  // darbeler arası azami boşluk
  rand int unsigned max_pulse    = 40;

  constraint c_sane {
    n_pulses  inside {[1:2000]};
    max_gap   inside {[1:2000]};
    max_pulse inside {[2:200]};
  }

  function new(string name = "irq_storm_seq");
    super.new(name);
  endfunction

  virtual task body();
    irq_item it;
    repeat (n_pulses) begin
      it = irq_item::type_id::create("it");
      start_item(it);
      if (!it.randomize() with {
            pre_delay inside {[0:local::max_gap]};
            pulse_len inside {[2:local::max_pulse]};
          })
        `uvm_error("IRQ_STORM", "irq_item randomize edilemedi")
      finish_item(it);
    end
  endtask

endclass : irq_storm_seq
