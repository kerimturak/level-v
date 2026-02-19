# CERES RISC-V — run_v5 Analiz Raporu ve run_v6 Yol Haritası

**Tarih**: 2026-02-19  
**Tasarım**: `ceres_wrapper` (SKY130, OpenLane 2023.09.07)  
**Referans**: `run_v5` — GDS başarılı, signoff kısmen tamamlandı

---

## 1. run_v5 Durum Özeti

| Metrik | Sonuç | Durum |
|--------|-------|-------|
| GDS çıktısı | 424 MB | ✅ Başarılı |
| Routing DRC | 0 violation | ✅ Temiz |
| Detaylı Routing wire length | 6,381,374 µm | ✅ |
| Via sayısı | 513,037 | ✅ |
| Instance sayısı | 2,510,059 (filler/decap dahil) | ✅ |
| Net sayısı | 61,763 | ✅ |
| **Typical corner** Setup WNS | **+3.42 ns** | ✅ MET |
| **Typical corner** Hold WNS | **+0.09 ns** | ✅ MET |
| **Slowest corner** Setup WNS | **-21.69 ns** | ❌ SAHTE (SRAM SS lib yok) |
| **Slowest corner** TNS | -42,833 ns (8687 path) | ❌ SAHTE |
| IR Drop raporu | Atlandı (`RUN_IRDROP_REPORT=0`) | ⚠️ |
| Magic LEF | Tamamlanmadı (OOM — 13.7 GB RAM) | ❌ |
| LVS | Çalışmadı (Magic LEF bağımlılığı) | ❌ |
| Antenna repair | Tamamlandı (GRT içinde) | ✅ |

### Akış Adımları (run_v5)

```
 1  Synthesis                    ✅  (4807 warn, 39 ABC errors — zararsız)
 2  STA (single-corner)         ✅  (25 warn — SRAM dout0 + unconstrained)
 3  Initial Floorplan           ✅  5488×5478 µm
 4  IO Placement                ✅
 5  Manual Macro Placement      ✅  26 SRAM makro
 6  Tap/Decap Insertion         ✅
 7  PDN Generation              ✅  (3x PDN-0110 via warning)
 8  Global Placement            ✅
 9  GPL STA                     ✅
10  Placement Resizer           ✅
11  Detailed Placement          ✅
12  DPL STA                     ✅
13  CTS                         ✅  (4896 pure-wire, zararsız)
14  CTS STA                     ✅
15  CTS Resizer                 ✅
16  GRT Resizer Design          ✅
17  RSZ Design STA              ✅
18  GRT Resizer Timing          ✅
19  RSZ Timing STA              ✅
20  Global Routing              ✅  (Antenna repair tamamlandı)
22  GRT STA                     ✅  (580 unconstrained endpoint)
23  Fill Insertion               ✅
24  Detailed Routing            ✅  0 DRC, 39 dakika, peak 12.8 GB RAM
25  Wire Length Check           ✅
26  SPEF Extraction (min)       ✅
27  MCSTA (min)                 ✅
28  SPEF Extraction (max)       ✅
29  MCSTA (max)                 ✅  (sahte violation — SRAM SS lib eksik)
30  SPEF Extraction (nom)       ✅
31  MCSTA (nom)                 ✅  (Typical +3.42ns, Slowest sahte fail)
32  Magic GDS                   ✅  424 MB
32  Magic LEF                   ❌  OOM/stuck (13.7 GB RAM, killed)
```

---

## 2. Uyarı Sınıflandırması

### 2.1 🔴 KRİTİK — SRAM Multi-Corner Liberty Eksikliği

- **Adet**: 3 corner × ~8700 path = ~26000 VIOLATED satırı
- **Belirti**: Slowest corner WNS = -21.69 ns, TNS = -42833 ns
- **Kök Neden**: SRAM makro için yalnızca **TT** (Typical, 1.8V, 25°C) Liberty mevcut.
  OpenSTA **SS** (Slow-Slow, düşük voltaj, yüksek sıcaklık) ve **FF** (Fast-Fast)
  corner'larda SRAM timing bilgisi bulamıyor → SRAM delay **0 ns** varsayılıyor →
  tüm SRAM path'leri sahte timing violation üretiyor.
- **Etki**: Multi-corner STA sonuçları güvenilmez. Tape-out yapılacaksa kabul edilemez.
- **Mevcut Liberty**: `sky130_sram_1kbyte_1rw1r_32x256_8_TT_1p8V_25C.lib`

### 2.2 🔴 KRİTİK — IR Drop Raporu Atlandı

- **Belirti**: `RUN_IRDROP_REPORT=0` config'de
- **Kök Neden**: PDN mesh ~1.6M node üretiyor → IR Drop solver 15+ GB RAM kullanıyor → OOM kill
- **Etki**: Güç ağı kalitesi doğrulanmamış. Çip üzerinde IR droop olabilir.

### 2.3 🟡 ORTA — Synthesis "Wire Has No Driver" Uyarıları

- **Adet**: 4807
- **Örnekler**:
  - `Wire cpu.\pipe[] is used but has no driver` (291×)
  - `Wire wb_interconnect.\wb_m_o[] is used but has no driver` (228×)
  - `Wire memory_arbiter.\iomem_req_o[] is used but has no driver` (179×)
  - `Wire dcache.\lowX_req_o[]` (166×), `icache.\cache_res_o[]` (131×)
  - `Wire cs_reg_file.\tdata_o[]` (128×), `reg_file.\r_data_o[]` (64×)
- **Kök Neden**: sv2v, SystemVerilog struct/interface bus'larını Verilog wire'lara çeviriyor.
  Yosys bazı bus parçalarını "undriven" görüyor — fakat sentez sonucu doğru çalışıyor.
- **Etki**: Fonksiyonel etki yok. Gürültü (noise) — run_v5 zaten doğru route etti.
- **Çözüm**: RTL'de struct default initialize veya sv2v post-processing script

### 2.4 🟡 ORTA — SRAM `dout0` Port Bulunamadı

- **Adet**: 24 (her SRAM instance için 1)
- **Belirti**: `port dout0 not found` — STA sırasında
- **Kök Neden**: Liberty'de `pin(dout0[31:0])` (bus notation) var, fakat sentez
  netlist'inde port'lar bit-blasted: `dout0[0]`, `dout0[1]`, ... `dout0[31]`.
  OpenSTA bus ismini bit-blasted isimlerle eşleştiremiyor.
- **Etki**: SRAM çıkış timing'i STA'da modellenmemiyor → SRAM sonrası path'ler yanlış
- **Çözüm**: Liberty dosyasını bit-blasted formata dönüştür

### 2.5 🟢 DÜŞÜK — STA `ccsn_pnlh` / `ccsn_ovrf` Template Uyarıları

- **Adet**: 46,288 (her 3 corner'da)
  - `ccsn_pnlh not found`: 22,960
  - `ccsn_ovrf not found`: 10,736
- **Kök Neden**: SKY130 Liberty dosyaları CCSN (Current Source) noise table'ları
  içeriyor, fakat OpenSTA bu noise modelini desteklemiyor.
- **Etki**: **Sıfır.** Noise analizi için olan bilgi — timing'i etkilemez.
- **Çözüm**: Görmezden gel. İsteğe bağlı: Liberty'den strip et.

### 2.6 🟢 DÜŞÜK — 580 Unconstrained Endpoint

- **Adet**: 580 port (timing constraint yok)
- **Kapsam**:
  - `gpio_o[0:31]`, `gpio_oe_o[0:31]` — 64 pin
  - `vga_r_o`, `vga_g_o`, `vga_b_o`, `vga_hsync_o`, `vga_vsync_o` — VGA
  - `pwm_o`, `pwm_n_o` — PWM
  - `spi0_mosi_o`, `spi0_sclk_o`, `spi0_ss_o` — SPI
  - `i2c0_scl_io`, `i2c0_sda_io` — I2C
  - `wdt_reset_o`, `status_led_o`, `cpu_halt_o`
  - SRAM `csb0`, `csb1`, `web0` pin'leri (26 makro × ~8 pin)
- **Kök Neden**: SDC dosyasında bu port'lara `set_output_delay` veya `set_false_path` tanımlanmamış.
- **Etki**: Bu pin'ler zamanlanamıyor → STA raporu eksik

### 2.7 🟢 DÜŞÜK — Diğer Uyarılar

| Uyarı | Adet | Kaynak | Açıklama |
|-------|------|--------|----------|
| `PDN-0110 No via met4↔met5` | 3 | PDN | Birkaç strap noktasında via yerleşemedi |
| `ABC: network is combinational` | 39 | Synthesis | ABC optimizer subcircuit'leri combinational gördü |
| `SRAM cell overlap in GDS` | ~100 | Magic | SRAM GDS'te duplicate contact_7 hücresi |
| `CTS-0043 pure wire` | 4896 | CTS | Buffer gerektirmeyen kısa clock wire'lar |
| `SPEF not connected to net` | 5748 | SPEF/STA | Parasitic node'lar SRAM etrafında bağlanamadı |
| `SRAM lib already exists` | 1 | STA | Aynı Liberty 2 kez yüklendi |

---

## 3. run_v6 Yol Haritası

### Faz 1: SRAM Liberty Düzeltmeleri (Kritik) — Öncelik 1

#### 1.1 SRAM SS/FF Corner Liberty Üretimi

**Sorun**: Yalnızca TT corner var → multi-corner STA sahte fail  
**Çözüm**: OpenRAM SRAM compiler'dan SS ve FF Liberty üret.

Eğer OpenRAM erişimi yoksa, **manual corner scaling** yapılabilir:

```bash
# SS (Slow-Slow) Liberty: delay'leri %30 artır, yeni lib üret
python3 scale_sram_liberty.py \
    --input  sky130_sram_..._TT_1p8V_25C.lib \
    --output sky130_sram_..._SS_1p6V_100C.lib \
    --delay_scale 1.30 \
    --slew_scale 1.35

# FF (Fast-Fast) Liberty: delay'leri %25 azalt
python3 scale_sram_liberty.py \
    --input  sky130_sram_..._TT_1p8V_25C.lib \
    --output sky130_sram_..._FF_1p95V_n40C.lib \
    --delay_scale 0.75 \
    --slew_scale 0.70
```

**config.tcl değişikliği**:
```tcl
set sram_lib_tt  "$sram_macro_dir/sky130_sram_..._TT_1p8V_25C.lib"
set sram_lib_ss  "$sram_macro_dir/sky130_sram_..._SS_1p6V_100C.lib"
set sram_lib_ff  "$sram_macro_dir/sky130_sram_..._FF_1p95V_n40C.lib"

set ::env(EXTRA_LIBS) [list $sram_lib_tt]

# Multi-corner SRAM Liberty
set ::env(STA_WRITE_LIB) 1
# OpenLane corner mapping:
#   min (fastest) → FF lib
#   nom (typical) → TT lib
#   max (slowest) → SS lib
```

#### 1.2 Liberty Pin Format Düzeltmesi (bit-blast)

**Sorun**: `pin(dout0[31:0])` bus notation → OpenSTA bit-blasted netlist ile eşleşemiyor  
**Çözüm**: Script ile Liberty'deki bus pin'leri bit-blasted formata dönüştür

```bash
# Mevcut:   pin(dout0[31:0]) { direction: output; ... }
# Hedef:    pin(dout0[0]) { direction: output; ... }
#           pin(dout0[1]) { direction: output; ... }
#           ...
#           pin(dout0[31]) { direction: output; ... }
```

Bu dönüşüm `generate_sram_macros.sh` script'ine eklenecek.

### Faz 2: SDC Constraints Tamamla — Öncelik 2

#### 2.1 Unconstrained Endpoint'leri Kapat

`constraint.sdc`'ye eklenecek bölüm:

```tcl
# ==============================================================
# 12. GPIO CONSTRAINTS
# ==============================================================
set_false_path -to [get_ports gpio_o[*]]
set_false_path -to [get_ports gpio_oe_o[*]]
set_false_path -from [get_ports gpio_i[*]]

# ==============================================================
# 13. VGA OUTPUT (slow pixel clock domain)
# ==============================================================
set_false_path -to [get_ports vga_r_o[*]]
set_false_path -to [get_ports vga_g_o[*]]
set_false_path -to [get_ports vga_b_o[*]]
set_false_path -to [get_ports vga_hsync_o]
set_false_path -to [get_ports vga_vsync_o]

# ==============================================================
# 14. PWM OUTPUT
# ==============================================================
set_false_path -to [get_ports pwm_o[*]]
set_false_path -to [get_ports pwm_n_o[*]]
set_false_path -from [get_ports pwm_fault_i]

# ==============================================================
# 15. SPI OUTPUT (async external device)
# ==============================================================
set_false_path -to [get_ports spi0_mosi_o]
set_false_path -to [get_ports spi0_sclk_o]
set_false_path -to [get_ports spi0_ss_o[*]]

# ==============================================================
# 16. JTAG / DEBUG (if present)
# ==============================================================
# set_false_path -from [get_ports jtag_*]
# set_false_path -to   [get_ports jtag_*]
```

**Hedef**: 580 unconstrained → 0

### Faz 3: IR Drop / PDN Optimizasyonu — Öncelik 3

#### 3.1 PDN Pitch Gevşetme

**Sorun**: Varsayılan PDN mesh çok yoğun → 1.6M node → OOM  
**Çözüm**: met4/met5 strap pitch'ini 2× artır, strap genişliğini koru

```tcl
# config.tcl'ye ekle:
set ::env(FP_PDN_VPITCH) 280
set ::env(FP_PDN_HPITCH) 280
set ::env(FP_PDN_VWIDTH) 3.1
set ::env(FP_PDN_HWIDTH) 3.1
set ::env(FP_PDN_VOFFSET) 16.32
set ::env(FP_PDN_HOFFSET) 16.65
```

**Beklenen etki**: PDN node sayısı ~1.6M → ~400K, RAM kullanımı ~4 GB'a düşer

#### 3.2 IR Drop'u Aktif Et

```tcl
set ::env(RUN_IRDROP_REPORT) 1
```

#### 3.3 Docker Memory Ayarı

```bash
# Makefile'da Docker komutu:
docker run --memory=14g --memory-swap=24g ...
```

### Faz 4: Config İyileştirmeleri — Öncelik 4

#### 4.1 GRT Antenna İterasyon Azaltma

```tcl
# 10 → 5 (run_v5'te 1 iterasyonda bitti zaten)
set ::env(GRT_ANT_ITERS) 5
```

#### 4.2 Sentinel Ayarları (Değişiklik Yok)

Aşağıdakiler korunacak:
```tcl
set ::env(SYNTH_NO_FLAT) 1           # Hiyerarşi koru (debug için)
set ::env(QUIT_ON_SYNTH_CHECKS) 0    # sv2v false positive'ler
set ::env(SYNTH_BUFFERING) 1         # Buffer ekleme aktif
set ::env(PL_ROUTABILITY_DRIVEN) 1   # Congestion-aware placement
set ::env(GRT_ALLOW_CONGESTION) 1    # Congestion toleransı
```

### Faz 5: Signoff Tamamla — Öncelik 5

#### 5.1 Magic LEF Sorunu

**Sorun**: Magic LEF generation 13.7 GB RAM kullanıp stuck kaldı  
**Çözüm seçenekleri**:
- Docker swap ile: `--memory-swap=24g`
- Magic'e `set GDS_FLATTEN 0` parametresi
- Alternatif: OpenROAD'un LEF yazıcısını kullan (daha hafif)

#### 5.2 LVS

Magic LEF tamamlandıktan sonra:
```bash
make asic_lvs ASIC_TAG=run_v6
```

#### 5.3 Antenna Check

run_v5'te GRT içinde tamamlandı. DRT sonrası tekrar kontrol:
```bash
make asic_antenna ASIC_TAG=run_v6
```

---

## 4. Uygulama Sırası ve Tahmini Etki

| # | İş Kalemi | Karmaşıklık | Tahmini Süre | Beklenen Etki |
|---|-----------|-------------|--------------|---------------|
| 1 | SRAM Liberty bit-blast (dout0) | Kolay | 1 saat | 24 STA uyarı gider, SRAM timing doğru olur |
| 2 | SRAM SS/FF corner Liberty üret | Orta | 2-3 saat | Multi-corner STA güvenilir hale gelir, ~26K sahte violation gider |
| 3 | SDC unconstrained endpoint'ler | Kolay | 30 dakika | 580 unconstrained → 0 |
| 4 | PDN pitch artır + IR Drop aç | Orta | 1 saat config + ~2 saat run | IR Drop raporu alınır |
| 5 | GRT_ANT_ITERS 10→5 | Trivial | 1 dakika | Küçük hız iyileşmesi |
| 6 | Magic LEF / LVS tamamla | Zor | 4+ saat (RAM bağımlı) | Tam signoff |
| 7 | Synth wire uyarıları (opsiyonel) | Zor | RTL değişiklik | 4807 uyarı azalır |

---

## 5. run_v6 config.tcl Değişiklik Planı

```diff
  # Mevcut (run_v5)                          → Yeni (run_v6)
  
  # SRAM Liberty
- set ::env(EXTRA_LIBS) [list $sram_lib]
+ set ::env(EXTRA_LIBS) [list $sram_lib_tt $sram_lib_ss $sram_lib_ff]

  # PDN
+ set ::env(FP_PDN_VPITCH) 280
+ set ::env(FP_PDN_HPITCH) 280

  # IR Drop
- set ::env(RUN_IRDROP_REPORT) 0
+ set ::env(RUN_IRDROP_REPORT) 1

  # Antenna
- set ::env(GRT_ANT_ITERS) 10
+ set ::env(GRT_ANT_ITERS) 5
```

---

## 6. Mevcut Config Referansı (run_v5)

```tcl
CLOCK_PERIOD        = 30.0 ns (33.3 MHz)
DIE_AREA            = 5500 × 5500 µm
PL_TARGET_DENSITY   = 0.30
PL_MACRO_HALO       = 30 30
PL_MACRO_CHANNEL    = 40 40
GRT_OVERFLOW_ITERS  = 50
GRT_ADJUSTMENT      = 0.2
GRT_ANT_ITERS       = 10
SYNTH_STRATEGY      = "AREA 1"
MAX_FANOUT_CONSTRAINT = 12
SYNTH_NO_FLAT       = 1
SYNTH_BUFFERING     = 1
```

---

## 7. Timing Referansı (run_v5, 3 corner)

| Corner | SPEF | Setup WNS | Setup TNS | Hold WNS | Geçerli? |
|--------|------|-----------|-----------|----------|----------|
| Fastest (FF) | min | +13.16 ns | 0 | +0.09 ns | ❌ (SRAM FF lib yok) |
| Typical (TT) | nom | +3.42 ns | 0 | +0.28 ns | ✅ |
| Slowest (SS) | max | -21.69 ns | -42833 ns | +0.83 ns | ❌ (SRAM SS lib yok) |

**Not**: Typical corner sonuçları güvenilir. SS/FF sonuçları SRAM Liberty eksikliğinden
dolayı sahte. SRAM path'lerinde delay=0 varsayımı yapılıyor.

---

*Bu doküman `run_v6` hazırlık referansı olarak oluşturulmuştur.*
