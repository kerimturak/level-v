// ============================================================================
// Level RISC-V UVM — Ortak Tipler ve Sabitler
// ----------------------------------------------------------------------------
// Paket genelinde kullanılan enum/parametreler. RTL'deki level_param
// paketinden bağımsız tutulmuştur ki testbench, RTL parametre değişimlerinde
// yalnızca buradaki sabitler üzerinden güncellensin.
// ============================================================================

// Cache satırı genişliği (bit) — RTL'deki BLK_SIZE=128 ile uyumlu olmalı.
localparam int LV_BLK_BITS  = 128;
localparam int LV_BLK_BYTES = LV_BLK_BITS / 8;  // 16

// Bellek haritası sabitleri (rtl/pkg/level_param.sv + pma.sv ile uyumlu)
localparam logic [31:0] LV_RESET_VECTOR   = 32'h8000_0000;  // Boot adresi
localparam logic [31:0] LV_RAM_BASE       = 32'h8000_0000;  // Cached RAM (PMA rwx)
localparam logic [31:0] LV_CLINT_BASE     = 32'h3000_0000;  // Uncached rw bölge
// tohost varsayılanı: BİLEREK uncached bölgede. Cached bölgede olsaydı,
// pass/fail yazması dcache'te kirli (dirty) satır olarak kalır ve eviction
// olmadan iomem'e hiç çıkmazdı -> scoreboard testin bittiğini göremezdi.
localparam logic [31:0] LV_TOHOST_DEFAULT = 32'h3000_1000;

// Rastgele programın veri (load/store) bölgesi varsayılanları
localparam logic [31:0] LV_DATA_BASE_DEFAULT     = 32'h8000_8000;  // cached
localparam int          LV_DATA_SIZE_DEFAULT     = 4096;           // bayt
localparam logic [31:0] LV_UNC_DATA_BASE_DEFAULT = 32'h3000_2000;  // uncached

// ----------------------------------------------------------------------------
// Bellek yanıt gecikmesi politikası — responder sequence'ın constraint'lerini
// tek enum ile şekillendirir. Testler bunu cfg üzerinden veya factory
// override ile değiştirerek aynı sequence'tan farklı zamanlama profilleri
// elde eder (ileri düzey teknik: "knob-driven constraint yönetimi").
// ----------------------------------------------------------------------------
typedef enum int {
  LV_LAT_ZERO,    // Hep minimum gecikme (1 çevrim) — en hızlı, hazırlık koşusu
  LV_LAT_SMALL,   // 1..4 çevrim — gerçekçi SRAM benzeri
  LV_LAT_RANDOM,  // 1..20 çevrim düz dağılım — genel stres
  LV_LAT_HEAVY,   // Ağırlıklı uzun gecikme + ara sıra çok uzun — backpressure
  LV_LAT_BURSTY   // Çoğu hızlı, arada uzun duraklamalar — cache miss fırtınası
} lv_lat_policy_e;

// Kesme türleri (irq_item için)
typedef enum int {
  LV_IRQ_TIMER = 0,  // timer_irq_i (MTIP)
  LV_IRQ_SW    = 1,  // sw_irq_i    (MSIP)
  LV_IRQ_EXT   = 2   // ext_irq_i   (MEIP)
} lv_irq_kind_e;

// Bellek işlem yönü
typedef enum bit {
  LV_MEM_READ  = 1'b0,
  LV_MEM_WRITE = 1'b1
} lv_mem_dir_e;
