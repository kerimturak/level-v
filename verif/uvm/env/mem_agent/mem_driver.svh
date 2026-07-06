// ============================================================================
// Level RISC-V UVM — Reaktif Bellek Sürücüsü (Slave Driver)
// ----------------------------------------------------------------------------
// Görevi bilinçli olarak "aptal" tutulmuştur: sequence'tan gelen yanıt
// tarifini (mem_rsp_item) alır, tarif edilen gecikme kadar bekler ve
// res_valid darbesini pin seviyesinde üretir. Yanıtın İÇERİĞİNE karar
// vermez — o iş responder sequence'ındır (bkz. mem_sequencer.svh açıklaması).
//
// İleri düzey teknik — UVM CALLBACK'leri:
//   mem_driver_cbs sanal sınıfı, yanıt sürülmeden hemen önce çağrılan bir
//   kanca (hook) tanımlar. Testler, driver'ı DEĞİŞTİRMEDEN bu kancaya
//   callback kaydedip gecikme ekleyebilir, veri bozabilir, log alabilir.
//   (örn. tests/level_v_test_lib.svh içindeki mem_extra_delay_cb)
// ============================================================================

typedef class mem_driver;

// Callback arayüzü: yanıt sürülmeden önce item üzerinde oynama izni verir.
class mem_driver_cbs extends uvm_callback;

  `uvm_object_utils(mem_driver_cbs)

  function new(string name = "mem_driver_cbs");
    super.new(name);
  endfunction

  // Varsayılan: hiçbir şey yapma. Türetilen callback'ler override eder.
  // `item` referans olduğundan latency/rdata değişiklikleri driver'a yansır.
  virtual task pre_response(mem_driver drv, mem_rsp_item item);
  endtask

endclass : mem_driver_cbs


class mem_driver extends uvm_driver #(mem_rsp_item);

  `uvm_component_utils(mem_driver)
  // Callback altyapısını bu sınıf için etkinleştir.
  `uvm_register_cb(mem_driver, mem_driver_cbs)

  virtual iomem_if vif;
  mem_agent_cfg    cfg;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual iomem_if)::get(this, "", "mem_vif", vif))
      `uvm_fatal("MEM_DRV", "iomem_if sanal arayuzu config_db'de yok")
    if (!uvm_config_db#(mem_agent_cfg)::get(this, "", "mem_cfg", cfg))
      `uvm_fatal("MEM_DRV", "mem_agent_cfg config_db'de yok")
  endfunction

  // NOT — Sürüş stili bilinçli olarak clocking block ÇIKIŞI değil, düz
  // @(posedge clk) + NBA'dır. Nedeni: CB çıkış sürüşlerinin "kenar sonrası
  // aynı zaman adımında verilen sürüş hangi kenara uygulanır" semantiği
  // simülatörler arasında farklılaşıyor (Verilator'da bir sonraki kenara
  // kayıyor ve @(cb) aynı adımda fall-through yapabiliyor). lat=1 gibi dar
  // pencerelerde assert+deassert aynı kenara binip darbeyi YOK EDEBİLİYOR.
  // Düz NBA sürüş her simülatörde deterministiktir: posedge T'de verilen
  // NBA, T+delta'da görünür ve DUT T+1 kenarında örnekler.
  // (Girişleri örnekleyen monitör mon_cb kullanmaya devam eder — sorun
  //  yalnızca CB ÇIKIŞ yolundaydı.)
  task run_phase(uvm_phase phase);
    mem_rsp_item item;

    // Reset boyunca yanıt hattını temizle.
    vif.res_valid <= 1'b0;
    vif.res_data  <= '0;
    vif.res_ready <= 1'b1;
    @(posedge vif.rst_n);

    forever begin
      // Sequence bir istek görmeden item üretmez; dolayısıyla burada
      // bloklanmak "bellek boşta" demektir.
      seq_item_port.get_next_item(item);

      // Callback kancası: kayıtlı tüm mem_driver_cbs'lerin pre_response'u
      // sırayla çağrılır — gecikme/veri üzerinde son söz hakkı onlarındır.
      `uvm_do_callbacks(mem_driver, mem_driver_cbs, pre_response(this, item))

      // Yanıt bekletilirken bellek "meşgul" görünür (bilgi amaçlı ready).
      vif.res_ready <= 1'b0;

      // Tarif edilen gecikme kadar çevrim bekle (en az 1 — item constraint'i
      // garanti eder; callback bozduysa yine de en az 1 çevrime yuvarla).
      repeat (item.latency > 0 ? item.latency : 1) @(posedge vif.clk);

      // Tek çevrimlik tamamlama darbesi. Yazmalarda rdata umursanmaz ama
      // deterministiklik için yine de sürülür.
      vif.res_valid <= 1'b1;
      vif.res_data  <= item.rdata;
      @(posedge vif.clk);
      vif.res_valid <= 1'b0;
      vif.res_ready <= 1'b1;

      seq_item_port.item_done();
    end
  endtask

endclass : mem_driver
