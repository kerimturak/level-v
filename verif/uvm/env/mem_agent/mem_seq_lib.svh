// ============================================================================
// Level RISC-V UVM — Reaktif Bellek Sequence Kütüphanesi
// ----------------------------------------------------------------------------
// mem_responder_seq: ortamın "bellek davranışı"nın tamamı. Sonsuz döngüde:
//   1) Monitörün sequencer FIFO'suna yazdığı ham isteği çeker,
//   2) Paylaşılan mem_model üzerinde yan etkiyi uygular
//      (yazma -> modeli güncelle, okuma -> modelden veri hesapla),
//   3) cfg'deki gecikme politikasına göre rastgele gecikmeli mem_rsp_item
//      üretip driver'a gönderir.
//
// Bellek SEMANTİĞİ (satır/uncached kuralları) mem_model'de, ZAMANLAMA
// buradaki randomize'da, PİN sürüşü driver'dadır — üç kaygı üç katmanda.
//
// mem_heavy_backpressure_seq: aynı sequence'ın factory override ile nasıl
// değiştirileceğini gösteren türev — testler
//   set_type_override_by_type(mem_responder_seq::get_type(),
//                             mem_heavy_backpressure_seq::get_type())
// dediğinde ortamın geri kalanı hiç değişmeden bellek "yavaşlar".
// ============================================================================

class mem_responder_seq extends uvm_sequence #(mem_rsp_item);

  `uvm_object_utils(mem_responder_seq)
  // p_sequencer makrosu: sequencer'daki req_fifo ve cfg'ye tipli erişim.
  `uvm_declare_p_sequencer(mem_sequencer)

  function new(string name = "mem_responder_seq");
    super.new(name);
  endfunction

  // Türevlerin zamanlamayı özelleştirmesi için ayrılmış kanca:
  // varsayılan, cfg'deki politikayı item'a kopyalamaktır.
  virtual function void shape_timing(mem_rsp_item item);
    item.set_policy(p_sequencer.cfg.lat_policy,
                    p_sequencer.cfg.lat_min,
                    p_sequencer.cfg.lat_max);
  endfunction

  virtual task body();
    mem_txn      req;
    mem_rsp_item rsp;
    mem_model    mdl = p_sequencer.cfg.model;

    // Sonsuz reaktif döngü: test bitişini objection'lar yönetir; bu
    // sequence hiç bitmez, driver'la birlikte "bellek" olarak yaşar.
    forever begin
      // 1) DUT'tan gelen bir sonraki isteği bekle (monitor -> FIFO).
      `uvm_info("MEM_RSP_SEQ", "fifo.get bekleniyor", UVM_HIGH)
      p_sequencer.req_fifo.get(req);
      `uvm_info("MEM_RSP_SEQ", $sformatf("istek alindi addr=0x%08h", req.addr),
                UVM_HIGH)

      // 2) Bellek yan etkisi + okuma verisi hesabı.
      rsp = mem_rsp_item::type_id::create("rsp");
      if (req.dir() == LV_MEM_WRITE) begin
        if (req.uncached)
          // Uncached yazma: word data[31:0]'da, strobe'lar satır pozisyonlu.
          mdl.write_uncached(req.addr, req.wdata[31:0], req.rw);
        else
          // Cached yazma (eviction / satır yazımı): pozisyonel strobe.
          mdl.write_line(req.addr, req.wdata, req.rw);
        rsp.rdata = '0;  // Yazma yanıtında veri anlamsız
      end else begin
        rsp.rdata = req.uncached ? mdl.read_uncached(req.addr)
                                 : mdl.read_line(req.addr);
      end

      // 3) Zamanlamayı politika ile şekillendir ve randomize et.
      shape_timing(rsp);
      start_item(rsp);
      if (!rsp.randomize())
        `uvm_error("MEM_RSP_SEQ", "mem_rsp_item randomize edilemedi")
      `uvm_info("MEM_RSP_SEQ", $sformatf("yanit sürülüyor lat=%0d", rsp.latency),
                UVM_HIGH)
      finish_item(rsp);
      `uvm_info("MEM_RSP_SEQ", "finish_item dondu", UVM_HIGH)
    end
  endtask

endclass : mem_responder_seq


// ----------------------------------------------------------------------------
// Ağır backpressure türevi — factory override tanıtımı için.
// shape_timing'i ezerek cfg ne derse desin HEAVY politika dayatır.
// ----------------------------------------------------------------------------
class mem_heavy_backpressure_seq extends mem_responder_seq;

  `uvm_object_utils(mem_heavy_backpressure_seq)

  function new(string name = "mem_heavy_backpressure_seq");
    super.new(name);
  endfunction

  virtual function void shape_timing(mem_rsp_item item);
    item.set_policy(LV_LAT_HEAVY, 10, 200);
  endfunction

endclass : mem_heavy_backpressure_seq
