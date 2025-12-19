# Fence.i Instruction Implementation for Dcache

## Overview

Bu dokümantasyon, RISC-V `fence.i` instruction'ının dcache tarafında nasıl implemente edildiğini açıklar. `fence.i` instruction'ı, instruction cache ile data cache arasında tutarlılık sağlamak için kullanılır.

## Problem Tanımı

RISC-V mimarisinde self-modifying code (kendini değiştiren kod) desteklenmektedir. Bir program, memory'ye yeni instruction yazabilir ve ardından bu instruction'ları execute edebilir. Bunun için:

1. Data cache'e yazılan yeni instruction'lar memory'ye flush edilmeli
2. Instruction cache invalidate edilmeli
3. Pipeline temizlenmeli

## Implementasyon Detayları

### 1. Dirty Array Register Yapısı

**Önceki Durum:** Dirty bit'ler SRAM içinde tutuluyordu, bu da tek cycle'da tüm dirty durumlarını görmeyi imkansız kılıyordu.

**Çözüm:** Dirty array'i register olarak tuttuk:

```systemverilog
// Dirty bits as register array for instant access
logic [NUM_WAY-1:0] dirty_reg_q [NUM_SET];
logic [NUM_WAY-1:0] dirty_reg_d [NUM_SET];
```

Bu sayede:
- Tek cycle'da herhangi bir set'in dirty durumunu okuyabiliyoruz
- Fence.i state machine'i için gerekli dirty taramasını hızlı yapabiliyoruz

### 2. Fence.i State Machine

Dcache için 8 state'li bir FSM implemente ettik:

```
FI_IDLE → FI_SCAN → FI_CHECK_WAY → FI_WRITEBACK_REQ → FI_WRITEBACK_WAIT → FI_MARK_CLEAN → FI_NEXT_WAY → FI_DONE
    ↑                     ↓                                                                              ↓
    └─────────────────────┴──────────────────────────────────────────────────────────────────────────────┘
```

| State | Açıklama |
|-------|----------|
| `FI_IDLE` | Bekleme durumu, fence.i sinyali beklenir |
| `FI_SCAN` | Set index'i ayarla, SRAM'a adres gönder |
| `FI_CHECK_WAY` | Mevcut set'te dirty way var mı kontrol et |
| `FI_WRITEBACK_REQ` | LowX interface üzerinden memory'ye yazma isteği gönder |
| `FI_WRITEBACK_WAIT` | Memory yazma işleminin tamamlanmasını bekle |
| `FI_MARK_CLEAN` | Dirty bit'i temizle |
| `FI_NEXT_WAY` | Sonraki way'e geç veya sonraki set'e ilerle |
| `FI_DONE` | İşlem tamamlandı, stall sinyalini kaldır |

### 3. Pipeline Stall Mekanizması

Fence.i işlemi sırasında pipeline'ı durdurmak için yeni bir stall tipi ekledik:

```systemverilog
// ceres_param.sv
typedef enum logic [2:0] {
    NO_STALL      = 0,
    DMEM_STALL    = 1,
    IMEM_STALL    = 2,
    MUL_STALL     = 3,
    DIV_STALL     = 4,
    FENCEI_STALL  = 5  // Yeni eklendi
} stall_e;
```

**Stall önceliği:** `FENCEI_STALL` en yüksek önceliğe sahip (diğer stall'lardan önce kontrol edilir).

### 4. Flush Sinyali Yönetimi

**Problem:** Fence.i geldiğinde hem icache flush hem dcache dirty writeback gerekiyor. Ancak ortak `flush` sinyali her iki cache'i de etkiliyor ve dcache tag'lerini hemen sıfırlıyordu - dirty writeback tamamlanmadan!

**Çözüm:** Dcache için fence.i aktifken flush yazımlarını engelledik:

```systemverilog
// Tag array write - fence.i sırasında flush yazımını engelle
for (int i = 0; i < NUM_WAY; i++) 
    tsram.way[i] = (flush && !fi_active) ? '1 : (cache_wr_way[i] && tag_array_wr_en);
```

### 5. Fence.i Başlatma Koşulu

Rising edge detection ile fence.i'yı güvenilir şekilde tespit ettik:

```systemverilog
logic flush_i_prev;
always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) flush_i_prev <= 1'b0;
    else         flush_i_prev <= flush_i;
end

wire fencei_rising_edge = flush_i && !flush_i_prev;
```

### 6. Pipe2 Flush Koşulu

**Problem:** Fence.i instruction'ı pipe2'de iken `fencei_flush` sinyali pipe2'yu flush ediyordu, bu da fence.i'nın kendisinin kaybolmasına neden oluyordu.

**Çözüm:** Pipe2 flush koşulundan `fencei_flush` kaldırıldı:

```systemverilog
// Önce (hatalı):
if (!rst_ni || ex_flush_en || priority_flush == 3 || priority_flush == 2 || fencei_flush)

// Sonra (düzeltilmiş):
if (!rst_ni || ex_flush_en || priority_flush == 3 || priority_flush == 2)
```

## Kullanılan Test

### rv32ui-p-fence_i

Bu test, fence.i instruction'ının doğru çalışıp çalışmadığını kontrol eder:

1. Memory'den instruction okur (örn: `0x80002000` adresinden)
2. Aynı adrese yeni instruction yazar (store)
3. `fence.i` execute eder
4. Yeni yazılan adrese jump eder
5. Yeni instruction'ın doğru execute edilip edilmediğini kontrol eder

**Test Akışı:**
```
PC=0x80000144: sh x13, 0x80002004  # Yeni instruction yaz (0x8693)
PC=0x8000014c: sh x11, 0x80002006  # Yeni instruction yaz (0x14d6)
PC=0x80000150: fence.i             # Dcache flush + Icache invalidate
PC=0x8000015c: jalr x6, x15        # 0x80002004'e jump
PC=0x80002004: addi x13, x13, 0x14d6  # Yeni yazılan instruction execute
```

## Kullanılmayan/Alternatif Yaklaşımlar

### 1. SRAM-based Dirty Array (Kullanılmadı)

**Sebep:** SRAM'dan okuma 1 cycle latency'ye sahip. Fence.i sırasında tüm set'leri taramak için çok fazla cycle gerekiyordu.

**Tercih edilen:** Register-based dirty array - O(1) erişim süresi.

### 2. Blocking Cache During Fence.i (Kısmen Kullanıldı)

Pipeline stall ile cache'i bloke ettik ama normal cache işlemlerinin state machine'i bozmadığından emin olduk.

### 3. Write-Through Cache (Kullanılmadı)

**Sebep:** Write-through cache'de her yazma işlemi doğrudan memory'ye gider, bu da fence.i'yı basitleştirir ama performansı düşürür.

**Tercih edilen:** Write-back cache - daha iyi performans, fence.i'da dirty writeback gerekir.

### 4. Invalidate-Only Approach (Kullanılmadı)

**Sebep:** Sadece cache invalidate etmek veri kaybına neden olur. Dirty data'lar memory'ye yazılmadan kaybolur.

**Tercih edilen:** Dirty writeback + invalidate.

## Dosya Değişiklikleri

| Dosya | Değişiklik |
|-------|------------|
| `rtl/core/mmu/cache.sv` | Fence.i state machine, dirty register array, fencei_stall_o port |
| `rtl/core/stage04_memory/memory.sv` | fencei_stall_o port passthrough |
| `rtl/core/cpu.sv` | FENCEI_STALL entegrasyonu, pipe2 flush düzeltmesi |
| `rtl/pkg/ceres_param.sv` | FENCEI_STALL enum değeri |
| `rtl/include/writeback_log.svh` | FENCEI_STALL logging koşulu |

## Test Sonucu

```
✅ MATCH | PC=0x80002004 INST=0x14d68693 x13 0x000001bc | PC=0x80002004 INST=0x14d68693 x13 0x000001bc
```

Test başarıyla geçti. Dcache dirty data'yı memory'ye yazdı ve icache yeni instruction'ı doğru şekilde fetch etti.

## Gelecek İyileştirmeler

1. **Parallel Dirty Scan:** Tüm set'lerdeki dirty bit'leri paralel tarayarak daha hızlı writeback
2. **Priority Encoder:** Birden fazla dirty way varsa öncelik sırası belirleme
3. **Writeback Buffer:** Ardışık writeback'leri buffer'layarak memory bandwidth kullanımını optimize etme
