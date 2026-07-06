// ============================================================================
// Level RISC-V UVM — Bellek İşlem (Transaction) Sınıfları
// ----------------------------------------------------------------------------
// İki sınıf tanımlanır:
//
//  1) mem_txn      : Monitörün gözlemlediği TAMAMLANMIŞ işlem (istek+yanıt).
//                    Analysis port üzerinden scoreboard/coverage'a akar.
//  2) mem_rsp_item : Reaktif responder sequence'ın driver'a gönderdiği YANIT
//                    tarifi (gecikme + veri). Rastgeleleştirilebilir alanlar
//                    ve gecikme politikası constraint'leri buradadır.
//
// Ayrım bilinçlidir: gözlem tipi ile uyarı (stimulus) tipi karışmaz;
// scoreboard yalnızca mem_txn görür, driver yalnızca mem_rsp_item sürer.
// ============================================================================

// ----------------------------------------------------------------------------
// Gözlemlenen işlem — monitörden scoreboard ve coverage'a
// ----------------------------------------------------------------------------
class mem_txn extends uvm_sequence_item;

  // İstek alanları (DUT'un sürdüğü)
  bit [31:0]  addr;
  bit [15:0]  rw;         // 0 -> okuma; !=0 -> byte-strobe'lu yazma
  bit         uncached;
  bit [127:0] wdata;      // Yazma verisi

  // Yanıt alanları (TB'nin sürdüğü)
  bit [127:0] rdata;      // Okuma verisi
  int unsigned latency;   // İstekten yanıta geçen çevrim sayısı

  // Zaman damgaları (debug/coverage için)
  time req_time;
  time rsp_time;

  `uvm_object_utils_begin(mem_txn)
    `uvm_field_int(addr,     UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(rw,       UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(uncached, UVM_DEFAULT)
    `uvm_field_int(wdata,    UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(rdata,    UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(latency,  UVM_DEFAULT | UVM_DEC)
  `uvm_object_utils_end

  function new(string name = "mem_txn");
    super.new(name);
  endfunction

  // Okuma mı yazma mı? (rw strobe'larının OR'u)
  function lv_mem_dir_e dir();
    return (rw != '0) ? LV_MEM_WRITE : LV_MEM_READ;
  endfunction

  function string convert2string();
    return $sformatf("%s %s addr=0x%08h rw=0x%04h lat=%0d wdata=0x%032h rdata=0x%032h",
                     (dir() == LV_MEM_WRITE) ? "WR" : "RD",
                     uncached ? "UNC" : "CHD",
                     addr, rw, latency, wdata, rdata);
  endfunction

endclass : mem_txn


// ----------------------------------------------------------------------------
// Responder yanıt tarifi — sequence'tan driver'a
// ----------------------------------------------------------------------------
class mem_rsp_item extends uvm_sequence_item;

  // Sequence'ın bellek modelinden hesapladığı okuma verisi.
  // (Yazma işlemlerinde umursanmaz ama yine de sürülür.)
  bit [127:0] rdata;

  // Rastgeleleştirilen yanıt gecikmesi (çevrim). Driver, isteği gördükten
  // sonra bu kadar çevrim bekleyip res_valid darbesini üretir. En az 1:
  // sıfır-çevrim (kombinasyonel) yanıt yalnızca gerçek SoC'taki PBUS
  // kısayoluna özgüdür ve burada modellenmez.
  rand int unsigned latency;

  // Constraint'leri şekillendiren politika — sequence, randomize etmeden
  // önce cfg'den kopyalar. rand DEĞİL: dışarıdan atanır.
  lv_lat_policy_e policy  = LV_LAT_SMALL;
  int unsigned    lat_min = 1;
  int unsigned    lat_max = 20;

  `uvm_object_utils_begin(mem_rsp_item)
    `uvm_field_int(rdata,   UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(latency, UVM_DEFAULT | UVM_DEC)
    `uvm_field_enum(lv_lat_policy_e, policy, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "mem_rsp_item");
    super.new(name);
  endfunction

  // --------------------------------------------------------------------------
  // Gecikme politikası constraint'leri
  // --------------------------------------------------------------------------
  // Tek rand alan üzerinde, politika enum'una göre farklı dağılımlar.
  // "dist" ile ağırlıklandırma: HEAVY'de uzun kuyruklu, BURSTY'de bimodal.
  constraint c_latency {
    latency >= 1;
    if (policy == LV_LAT_ZERO) {
      latency == 1;
    } else if (policy == LV_LAT_SMALL) {
      latency inside {[1:4]};
    } else if (policy == LV_LAT_RANDOM) {
      latency inside {[lat_min:lat_max]};
    } else if (policy == LV_LAT_HEAVY) {
      // Ağırlıklı uzun gecikme: cache miss'lerin maliyetini abartıp
      // hazard/stall mantığını ve store buffer'ı zorlar.
      latency dist { [10:30] :/ 70, [31:80] :/ 25, [81:200] :/ 5 };
    } else { // LV_LAT_BURSTY
      // Bimodal: çoğunluk çok hızlı, azınlık çok yavaş — pipeline'ın
      // hızlı-yavaş geçişlerindeki kontrol yollarını gıdıklar.
      latency dist { 1 :/ 60, [2:4] :/ 20, [40:120] :/ 20 };
    }
  }

  // Politika + sınırları tek çağrıda ayarlayan yardımcı.
  function void set_policy(lv_lat_policy_e p, int unsigned mn, int unsigned mx);
    policy  = p;
    lat_min = mn;
    lat_max = mx;
  endfunction

endclass : mem_rsp_item
