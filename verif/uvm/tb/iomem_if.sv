// ============================================================================
// Level RISC-V — UVM iomem Arayüzü
// ----------------------------------------------------------------------------
// Çekirdeğin (cpu.sv) dış dünyaya açılan tek bellek kapısı olan
// iomem_req_t / iomem_res_t protokolünü UVM tarafına taşıyan interface.
//
// Protokol özeti (memory_arbiter.sv + wb_master_bridge.sv davranışından):
//   * Çekirdek `req_valid`'i kaldırır ve yanıt (`res_valid` darbesi) gelene
//     kadar isteği SABİT tutar (arbiter isteği register'da kilitler).
//   * Aynı anda en fazla 1 bekleyen işlem vardır (I$/D$ arbiter'da serileşir).
//   * `req_rw != 0`  -> yazma. 16 bit'lik byte-strobe, 128-bit satır üzerinde
//     pozisyoneldir; uncached yazmada strobe'lar addr[3:0] kadar kaydırılmış,
//     yazılacak word ise DAİMA data[31:0]'dadır (dcache böyle üretir).
//   * Cached okuma  -> 16 byte hizalı satırın tamamı döner.
//   * Uncached okuma-> adreslenen word, wb_master_bridge uyumluluğu için
//     4 lane'in DÖRDÜNE de kopyalanarak döner.
//   * `res_valid` tek çevrimlik bir darbedir ve isteği tamamlar/temizler.
//
// İçerik:
//   * Sürücü (responder) ve monitör için ayrı clocking block'lar
//     -> çevrim-hassas, yarış(race)-içermeyen örnekleme/sürüş.
//   * Protokol SVA'ları (assert property) — RTL'deki bir protokol ihlalini
//     testten bağımsız, anında yakalar. `+iomem_assert_off` ile kapatılabilir.
// ============================================================================
`timescale 1ns / 1ps

interface iomem_if (
    input logic clk,
    input logic rst_n
);

  // --------------------------------------------------------------------------
  // Sinyaller — iomem_req_t / iomem_res_t alanlarının bire bir açılımı.
  // Struct yerine düz sinyal kullanıyoruz ki UVM driver/monitor'da tek tek
  // sürülebilsin/örneklenebilsin; tb_top'ta struct'a paketlenir.
  // --------------------------------------------------------------------------
  // İstek kanalı (DUT -> TB, çekirdek master)
  logic         req_valid;     // İstek geçerli (yanıta kadar sabit kalır)
  logic         req_ready;     // Çekirdek her zaman 1 sürer (bilgi amaçlı)
  logic [ 15:0] req_rw;        // Byte-strobe; !=0 ise yazma, ==0 ise okuma
  logic [ 31:0] req_addr;      // Bayt adresi
  logic [127:0] req_data;      // Yazma verisi (cache satırı / word lane-0)
  logic         req_uncached;  // 1 = cache'i atlayan (tekil word) erişim

  // Yanıt kanalı (TB -> DUT, bellek modeli slave)
  logic         res_valid;     // Tek çevrimlik tamamlama darbesi
  logic         res_ready;     // Bellek yeni istek kabul edebilir (bilgi amaçlı)
  logic [127:0] res_data;      // Okuma verisi (yazmada umursanmaz)

  // --------------------------------------------------------------------------
  // Clocking block'lar
  // --------------------------------------------------------------------------
  // drv_cb: Reaktif bellek sürücüsü bu blok üzerinden yanıt sürer.
  //   * input  -> istek tarafını örnekler (1step önce, örnekleme yarışı yok)
  //   * output -> yanıt tarafını sürer (clock kenarından sonra, hold ihlali yok)
  clocking drv_cb @(posedge clk);
    default input #1step output #1ps;
    input  req_valid, req_rw, req_addr, req_data, req_uncached;
    output res_valid, res_ready, res_data;
  endclocking

  // mon_cb: Monitör her iki yönü de sadece örnekler (asla sürmez).
  clocking mon_cb @(posedge clk);
    default input #1step;
    input req_valid, req_ready, req_rw, req_addr, req_data, req_uncached;
    input res_valid, res_ready, res_data;
  endclocking

  // Modport'lar: yanlış yönde sürmeyi derleme zamanında engeller.
  modport DRV (clocking drv_cb, input clk, rst_n);
  modport MON (clocking mon_cb, input clk, rst_n);

  // --------------------------------------------------------------------------
  // Protokol Assertion'ları (SVA)
  // --------------------------------------------------------------------------
  // Assertion'lar plusarg ile topluca kapatılabilir (ör. bilinçli hata
  // enjeksiyonu yapan bir testte): +iomem_assert_off
  bit assert_en = 1'b1;
  initial begin
    if ($test$plusargs("iomem_assert_off")) begin
      assert_en = 1'b0;
      $display("[iomem_if] Protokol assertion'lari plusarg ile KAPATILDI");
    end
  end

  // A1: İstek, yanıt gelene kadar sabit kalmalı.
  //     (arbiter isteği kilitler; adres/veri/strobe değişirse RTL hatasıdır)
  property p_req_stable_until_res;
    @(posedge clk) disable iff (!rst_n || !assert_en)
    (req_valid && !res_valid) |=>
      (req_valid && $stable(req_addr) && $stable(req_rw) &&
       $stable(req_uncached) && $stable(req_data));
  endproperty
  a_req_stable : assert property (p_req_stable_until_res)
    else $error("[iomem_if] Istek yanittan once degisti! addr=%08h", req_addr);

  // A2: İstek yokken yanıt gelmemeli (sahipsiz/orphan yanıt).
  a_no_orphan_res : assert property (
    @(posedge clk) disable iff (!rst_n || !assert_en)
    res_valid |-> req_valid)
    else $error("[iomem_if] Istek yokken res_valid darbesi!");

  // A3: Geçerli istekte kontrol sinyalleri X/Z olmamalı.
  a_req_known : assert property (
    @(posedge clk) disable iff (!rst_n || !assert_en)
    req_valid |-> (!$isunknown(req_addr) && !$isunknown(req_rw) &&
                   !$isunknown(req_uncached)))
    else $error("[iomem_if] Gecerli istekte X/Z sinyal!");

  // A4: Cached (satır) erişimler 16 byte hizalı olmalı.
  //     Uncached erişimler word/half/byte hizasında gelebilir.
  a_cached_aligned : assert property (
    @(posedge clk) disable iff (!rst_n || !assert_en)
    (req_valid && !req_uncached) |-> (req_addr[3:0] == 4'h0))
    else $error("[iomem_if] Cached istek 16B hizali degil! addr=%08h", req_addr);

  // A5: Yazma isteğinde yazma verisi X olmamalı (strobe'lu byte'lar).
  a_wdata_known : assert property (
    @(posedge clk) disable iff (!rst_n || !assert_en)
    (req_valid && (req_rw != '0) && !req_uncached) |-> !$isunknown(req_data))
    else $error("[iomem_if] Cached yazmada X iceren veri! addr=%08h", req_addr);

  // --------------------------------------------------------------------------
  // Düşük seviye el sıkışma izleyici (+iomem_dbg ile açılır) — dalga dosyası
  // alınamayan/istenmeyen durumlarda pin hareketini zaman damgalı loglar.
  // --------------------------------------------------------------------------
  initial begin
    if ($test$plusargs("iomem_dbg")) begin
      fork
        forever @(res_valid)
          $display("[IOMEM_DBG] %0t res_valid -> %b (data=%h)",
                   $time, res_valid, res_data[31:0]);
        forever @(req_valid)
          $display("[IOMEM_DBG] %0t req_valid -> %b (addr=%h)",
                   $time, req_valid, req_addr);
      join
    end
  end

  // C1: Basit el sıkışma coverage'ı — istek/yanıt hiç örtüştü mü, arka arkaya
  //     istek geldi mi gibi durumları assertion cover'ları ile işaretle.
  c_back_to_back : cover property (
    @(posedge clk) disable iff (!rst_n)
    res_valid ##1 req_valid);

  c_uncached_write : cover property (
    @(posedge clk) disable iff (!rst_n)
    req_valid && req_uncached && (req_rw != '0));

endinterface : iomem_if
