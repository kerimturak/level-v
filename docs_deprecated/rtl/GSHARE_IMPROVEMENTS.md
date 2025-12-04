# GSHARE Branch Predictor İyileştirmeleri

## Özet

CERES RISC-V işlemcisinin branch predictor'ı basit GSHARE'den **Tournament Predictor** mimarisine yükseltildi. Bu döküman yapılan iyileştirmeleri ve sonuçları açıklar.

## Performans Karşılaştırması

### Önceki Sonuçlar (Basit GSHARE)
| Test | Toplam Doğruluk | Conditional Branch |
|------|-----------------|-------------------|
| branch_test | ~64% | ~63% |
| loop_test | ~65% | ~64% |

### Yeni Sonuçlar (Tournament Predictor)
| Test | Toplam Doğruluk | Conditional Branch |
|------|-----------------|-------------------|
| branch_test | **96.26%** | **92.36%** |
| loop_test | **97.48%** | **94.95%** |

**İyileşme: +32% toplam doğruluk artışı**

---

## Mimari Değişiklikler

### 1. Tournament Predictor

Tek GSHARE predictor yerine üç predictor birleştirildi:

```
                    ┌─────────────┐
                    │   Choice    │
                    │  Predictor  │
                    └──────┬──────┘
                           │ Select
              ┌────────────┴────────────┐
              ▼                         ▼
       ┌─────────────┐           ┌─────────────┐
       │   GSHARE    │           │   Bimodal   │
       │  Predictor  │           │  Predictor  │
       └─────────────┘           └─────────────┘
              │                         │
              └──────────┬──────────────┘
                         ▼
                  Final Prediction
```

#### GSHARE Predictor
- PC XOR GHR ile indeksleme
- Global branch korelasyonunu yakalar
- Karmaşık branch pattern'lerinde etkili

#### Bimodal Predictor  
- Sadece PC ile indeksleme
- Yerel branch davranışını yakalar
- Basit döngülerde etkili

#### Choice Predictor
- 2-bit saturating counter
- Sadece predictor'lar farklı tahmin yaptığında güncellenir
- Doğru olan predictor'a doğru eğitilir

### 2. Loop Predictor

Döngüleri tanımlamak ve tahmin etmek için özel bir yapı:

```systemverilog
localparam int LOOP_SIZE = 16;
logic [7:0] loop_count [LOOP_SIZE];  // Mevcut iterasyon
logic [7:0] loop_trip  [LOOP_SIZE];  // Görülen maksimum iterasyon
logic       loop_valid [LOOP_SIZE];
```

**Çalışma Prensibi:**
1. Backward branch alındığında `loop_count` artırılır
2. Backward branch alınmadığında (loop exit) `loop_trip` = `loop_count` kaydedilir
3. Sonraki çalışmalarda `loop_count >= loop_trip - 1` olduğunda exit tahmin edilir

### 3. Speculative GHR

```systemverilog
logic [GHR_SIZE-1:0] ghr;       // Committed GHR
logic [GHR_SIZE-1:0] ghr_spec;  // Speculative GHR
```

- Prediction yapıldığında `ghr_spec` güncellenir
- Misprediction durumunda `ghr` değerine restore edilir
- Daha agresif speculation sağlar

### 4. BTFN (Backward Taken, Forward Not-taken) Heuristic

BTB miss durumunda statik tahmin:
- **Backward branch (imm < 0):** Taken tahmin et (döngü olasılığı yüksek)
- **Forward branch (imm >= 0):** Not-taken tahmin et

---

## Yeni Veri Yapıları

### Bimodal Table
```systemverilog
logic [1:0] bimodal [PHT_SIZE];  // 2-bit saturating counter
```

### Choice Table
```systemverilog
logic [1:0] choice [PHT_SIZE];   // 2'b1x = GSHARE, 2'b0x = Bimodal
```

### Loop Predictor Tables
```systemverilog
logic [7:0] loop_count [LOOP_SIZE];
logic [7:0] loop_trip  [LOOP_SIZE];
logic       loop_valid [LOOP_SIZE];
logic [TAG] loop_tag   [LOOP_SIZE];
```

---

## Prediction Öncelik Sırası

1. **RAS (Return Address Stack)** - Function return'ler için
2. **JAL** - Unconditional direct jump, her zaman doğru
3. **JALR + IBTC hit** - Indirect jump, cache'lenmiş hedef
4. **Loop Predictor** - Backward branch + loop hit
5. **Tournament (GSHARE vs Bimodal)** - BTB hit durumunda
6. **BTFN Static** - BTB miss durumunda heuristic
7. **Sequential** - Default: PC + 4

---

## Update Politikası

### PHT Update (GSHARE)
```systemverilog
if (ex_was_taken)
  pht[idx] <= (pht[idx] < 2'b11) ? pht[idx] + 1 : pht[idx];
else
  pht[idx] <= (pht[idx] > 2'b00) ? pht[idx] - 1 : pht[idx];
```

### Choice Update
Sadece predictor'lar farklı tahmin yaptığında:
```systemverilog
if (pht[idx][1] != bimodal[idx][1]) begin
  if (pht[idx][1] == ex_was_taken)
    choice[idx]++;  // GSHARE doğru
  else
    choice[idx]--;  // Bimodal doğru
end
```

### Loop Update
```systemverilog
if (backward_branch && taken)
  loop_count[idx]++;
else if (backward_branch && !taken)
  loop_trip[idx] = loop_count[idx];  // Exit noktası kaydedildi
```

---

## Parametre Ayarları

`ceres_param.sv` içinde:

```systemverilog
// Branch Predictor Parameters
localparam int PHT_SIZE  = 256;   // Pattern History Table entries
localparam int BTB_SIZE  = 128;   // Branch Target Buffer entries
localparam int GHR_SIZE  = 12;    // Global History Register bits
localparam int IBTC_SIZE = 32;    // Indirect Branch Target Cache
localparam int RAS_SIZE  = 8;     // Return Address Stack depth
```

Loop predictor size (gshare_bp.sv içinde):
```systemverilog
localparam int LOOP_SIZE = 16;
```

---

## Test Sonuçları

### Custom Tests
```
branch_test:
  Total Control Transfers : 641
  Correct Predictions     : 617 (96.26%)
  Conditional Branch      : 290/314 (92.36%)

loop_test:
  Total Control Transfers : 636
  Correct Predictions     : 620 (97.48%)
  Conditional Branch      : 301/317 (94.95%)
```

### Component Breakdown
| Component | Accuracy |
|-----------|----------|
| JAL       | 100%     |
| JALR/RAS  | 100%     |
| Conditional | 92-95% |

---

## Gelecek İyileştirmeler

1. **TAGE Predictor** - Daha sofistike tagged geometric history
2. **Perceptron Predictor** - Neural network tabanlı
3. **Daha büyük tablolar** - PHT_SIZE = 512, BTB_SIZE = 256
4. **Branch confidence** - Düşük güvenli tahminlerde stall

---

## Dosya Değişiklikleri

- `rtl/core/stage01_fetch/gshare_bp.sv` - Tournament predictor implementasyonu
- `rtl/pkg/ceres_param.sv` - Merkezi parametre tanımları

---

## Referanslar

1. McFarling, S. "Combining Branch Predictors" (1993)
2. Yeh, T. & Patt, Y. "Alternative Implementations of Two-Level Adaptive Branch Prediction"
3. RISC-V Processors: BOOM, CVA6, Rocket Chip branch predictor implementations
