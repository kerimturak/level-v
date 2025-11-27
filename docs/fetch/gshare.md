Harika! Aşağıda, ceres işlemcinde kullandığın `gshare_bp` modülüne özel olarak hazırlanmış, **Gshare Branch Predictor** üzerine kapsamlı bir Markdown rehberi yer alıyor. Bu rehber tüm temel bilgileri, çalışma prensibini, tasarım ayrıntılarını ve ceres'daki uygulamanı kapsar. 

---

# 🧠 Gshare Branch Predictor – Derinlemesine Rehber

> **ceres RISC-V İşlemcisi – Global History-Based Branch Prediction**

---

## 📌 İçindekiler

1. [Giriş: Branch Prediction Nedir?](#1-giriş-branch-prediction-nedir)
2. [Gshare Predictor Nedir?](#2-gshare-predictor-nedir)
3. [Temel Yapılar: GHR, PHT, BTB](#3-temel-yapılar-ghr-pht-btb)
4. [Gshare Çalışma Prensibi](#4-gshare-çalışma-prensibi)
5. [ceres'da Gshare Uygulaması](#5-ceresda-gshare-uygulaması)
6. [Pipeline'da Gshare Entegrasyonu](#6-pipelineda-gshare-entegrasyonu)
7. [Speculative Execution & Restore](#7-speculative-execution--restore)
8. [Performans Gözlemi ve İyileştirme Fikirleri](#8-performans-gözlemi-ve-iyileştirme-fikirleri)

---

## 1️⃣ Giriş: Branch Prediction Nedir?

Modern işlemcilerde, özellikle **pipelined** mimarilerde, dallanma (branch) komutları verimliliği düşürür.

```assembly
beq x1, x2, label   // tahmin edilmezse, pipeline durur
```

🎯 **Amaç:** Branch'in alınıp alınmayacağını *tahmin etmek*, böylece pipeline’ı boşa doldurmamaktır.

---

## 2️⃣ Gshare Predictor Nedir?

**Gshare**, global history tabanlı bir branch prediction tekniğidir.

🔗 Temel fikir:
- PC’nin bazı bitleri ile GHR (Global History Register) XOR’lanarak bir index elde edilir.
- Bu index, **PHT (Pattern History Table)** üzerinden bir tahmin üretir.

🧠 Bu sayede global geçmiş bilgisi ile lokal adres bilgisi birleştirilir.

---

## 3️⃣ Temel Yapılar: GHR, PHT, BTB

| Bileşen | Açıklama |
|--------|----------|
| 🧬 GHR (Global History Register) | Son `n` adet branch'in alınıp alınmadığını tutar (`0/1`) |
| 📊 PHT (Pattern History Table)   | 2-bit saturating counters (`00` Strong NT, `11` Strong Taken) |
| 📍 BTB (Branch Target Buffer)    | Alınan branch'in hedef PC'sini saklar |

---

## 4️⃣ Gshare Çalışma Prensibi

### 🔁 Tahmin Aşaması

1. `pc[clog2(PHT_SIZE):1]` ile `ghr[clog2(PHT_SIZE)-1:0]` XOR'lanır → `pht_rd_idx`
2. `pht[pht_rd_idx]` değeri:
   - `10`, `11`: **Taken**
   - `00`, `01`: **Not taken**
3. Eğer taken ise → BTB'den hedef adres alınır.

### 🔁 Güncelleme Aşaması

1. Tahmin edilen branch emekli edilirken:
   - Eğer gerçekten taken ise `pht[pht_wr_idx]++` (max 2'b11)
   - Değilse `pht[pht_wr_idx]--` (min 2'b00)
2. `ghr <= {ghr[GH-2:0], outcome}`
3. BTB güncellenir (sadece taken branch'ler için)

---

## 5️⃣ ceres'da Gshare Uygulaması

```systemverilog
pht_rd_idx = pc_i[$clog2(PHT_SIZE):1] ^ ghr[$clog2(PHT_SIZE)-1:0];
branch.taken = (btb_pc[btb_rd_idx] == pc_i[31:$clog2(PHT_SIZE)+1]) && (pht[pht_rd_idx][1]);
```

### ✅ GHR
```systemverilog
ghr <= ex_taken ? {ghr[GHR_SIZE-2:0], pht_bit1[1] & spec_hit_i} : pht_ptr >>> ghr;
```

### ✅ PHT Update
```systemverilog
if (ex_taken)
  if (pht[pht_wr_idx] < 2'b11) pht[pht_wr_idx]++;
else
  if (pht[pht_wr_idx] > 2'b00) pht[pht_wr_idx]--;
```

### ✅ BTB Update
```systemverilog
btb_target[btb_wr_idx] <= ex_taken ? pc_target_i : '0;
btb_pc[btb_wr_idx]     <= ex_taken ? stage_pc[1][31:$clog2(PHT_SIZE)+1] : '0;
```

---

## 6️⃣ Pipeline'da Gshare Entegrasyonu

| Aşama | Gshare Etkisi |
|-------|----------------|
| **IF**  | `pht` + `btb` kullanılarak tahmin yapılır |
| **ID**  | `jal`, `ret`, `jalr` ayrıştırılır |
| **EX**  | Tahminin doğru olup olmadığı belirlenir |
| **MEM** | BTB update yok |
| **WB**  | Tahmin istatistiği yazılır (ceres'da ayrı counter yok) |

---

## 7️⃣ Speculative Execution & Restore

### 🧩 Sorun:
- Speculative olarak yapılan tahmin yanlış çıkabilir → Flush + RAS restore gerekebilir

### ✅ Çözüm:
```systemverilog
restore_ras = !stall_i && !spec_hit_i && ras_taken_q[0];
```

- Eğer `ras` üzerinden yapılan tahmin yanlışsa, `stage_pc[0]` ile RAS restore edilir
- Flush edilen pipeline tekrar başlatılır

---

## 8️⃣ Performans Gözlemi ve İyileştirme Fikirleri

### 📊 Başlangıç Ayarı
```systemverilog
pht <= '{default: 2'b01};  // Weakly Not Taken
```

### 🚀 İyileştirme Önerileri

| Yöntem                 | Açıklama                                      |
|------------------------|-----------------------------------------------|
| 1. PHT Entry Reset     | Flush sonrası belirli PHT girişlerini temizlemek |
| 2. GHR Boyutu Artışı   | Daha uzun geçmiş daha doğru tahmin sağlar     |
| 3. BTB Tag Ekle        | `btb_pc` yerine tam adres tag’leme yapılabilir |
| 4. Local+Global Hybrid | Gshare + Local Predictor kombinasyonu         |
| 5. TAGE veya Perceptron| Daha karmaşık ama güçlü tahmin yöntemleri     |

---

## ✅ Özet

| Yapı    | Açıklama                                      |
|---------|-----------------------------------------------|
| GHR     | Son branch sonuçlarını tutar (`1` = taken)    |
| PHT     | 2-bit counter ile tahmin üretir               |
| BTB     | Alınan branch için hedef adresi tutar         |
| Gshare  | PC ile GHR'i XOR'layarak index oluşturur      |
| Restore | Yanlış spekülatif tahminlerde geri alma       |

---

Eğer istersen bu rehberi `.md` formatında dosya haline getirebilirim veya README'ne ekleyebilirim.  
Ayrıca bu predictor için özel test senaryoları veya coverage analizleri de çıkarabiliriz.  
Devam etmek ister misin?