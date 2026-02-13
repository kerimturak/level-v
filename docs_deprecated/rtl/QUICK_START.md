---
title: "RTL Documentation - Quick Start"
description: "Hızlı başlangıç ve navigasyon rehberi"
date: 2025-12-01
draft: false
weight: 10
---

# 🚀 RTL Documentation - Hızlı Başlangıç

Ceres RISC-V RTL belgelerine hoşgeldiniz. Burada doğru başlangıç noktasını bulabilirsiniz.

---

## ⚡ 30 Saniye Kurulumu

```bash
# Doküman dizinine gidin
cd /home/kerim/level-v/docs/rtl

# Ana index'i açın
cat INDEX.md        # Tüm belgeler hakkında
# VEYA
cat README.md       # RTL modüllerine özel
```

---

## 🎯 Benim Durumum Ne?

### 👨‍🎓 Tamamen Yeni Başlayanım (RISC-V/Pipeline ilk kez)

**Süresi**: ~6 saat | **Sayfa**: ~260

```
1. docs/architecture.md          (30 min)
   └─ Architecture basics
   
2. docs/rtl/INDEX.md             (10 min)
   └─ Bugün neler öğreneceğiniz
   
3. docs/rtl/RTL_OVERVIEW.md      (30 min)
   └─ RTL yapısı ve modüller
   
4. docs/rtl/CERES_WRAPPER.md     (45 min)
   └─ Sistem entegrasyonu
   
5. docs/rtl/CPU_TOP_MODULE.md    (45 min)
   └─ Pipeline nasıl çalışır
   
6. docs/rtl/stages/FETCH_STAGE.md         (45 min)
7. docs/rtl/stages/DECODE_STAGE.md        (45 min)
8. docs/rtl/stages/EXECUTE_STAGE.md       (60 min)
9. docs/rtl/stages/MEMORY_WRITEBACK_STAGES.md (45 min)
   └─ Her stage detaylı
   
10. docs/rtl/HAZARD_UNIT.md      (45 min)
    └─ Pipeline güvenliği
```

✅ **Sonuç**: Tam Pipeline anlayışı

---

### 🎓 Orta Seviye (Pipeline temellerini biliyorum)

**Süresi**: ~2-4 saat | **Sayfa**: ~50-100

```
1. docs/rtl/README.md            (10 min)
   └─ Modül haritası

2. docs/rtl/CERES_WRAPPER.md +
   docs/rtl/CPU_TOP_MODULE.md    (1.5 hours)
   └─ System & Pipeline

3. İlgilendiğiniz stage:         (1-2 hours)
   ├─ FETCH_STAGE.md            (ALU/instruction?)
   ├─ DECODE_STAGE.md           (register/immediate?)
   ├─ EXECUTE_STAGE.md          (computation?)
   └─ MEMORY_WRITEBACK_STAGES.md (load/store?)

4. docs/rtl/HAZARD_UNIT.md       (30 min)
   └─ Side effects
```

✅ **Sonuç**: Spesifik modüler bilgi

---

### 🚀 İleri Seviye (Bug fix, optimization, yeni feature)

**Süresi**: ~30 min - 2 saat | **Sayfa**: ~20-50

```
HIZLI BAŞLANGAÇ:

1. docs/rtl/README.md (5 min)
   ↓ Modül tablosu kullanarak
   
2. İlgili belgeyi aç:
   └─ Örn: EXECUTE_STAGE.md ALU başlığına git
   
3. docs/rtl/HAZARD_UNIT.md (10 min)
   └─ Yan etkileri kontrol et
```

✅ **Sonuç**: Hızlı problem çözümü

---

## 📍 Konuma Göre Navigasyon

### "Pipeline nasıl çalışır?"
→ `docs/rtl/CPU_TOP_MODULE.md`

### "Instruction'ı decode nasıl yapıyorum?"
→ `docs/rtl/stages/DECODE_STAGE.md`

### "ALU işlemleri neler?"
→ `docs/rtl/stages/EXECUTE_STAGE.md` → ALU bölümü

### "Load/Store nasıl işliyor?"
→ `docs/rtl/stages/MEMORY_WRITEBACK_STAGES.md`

### "Branch nasıl çalışıyor?"
→ `docs/rtl/stages/FETCH_STAGE.md` (prediction)
→ `docs/rtl/stages/EXECUTE_STAGE.md` (resolution)

### "Veri hazardları nasıl çözülüyor?"
→ `docs/rtl/HAZARD_UNIT.md`

### "Register forwarding nedir?"
→ `docs/rtl/HAZARD_UNIT.md` → Data Forwarding bölümü

### "Pipeline neden duruyor?"
→ `docs/rtl/HAZARD_UNIT.md` → Stalling bölümü

### "Sistem memory map'i nedir?"
→ `docs/rtl/CERES_WRAPPER.md` → Memory Map bölümü

---

## 🗂️ Dosya Yapısı

```
📁 /home/kerim/level-v/docs/rtl/

📄 INDEX.md              ← Tüm belgeler arasında geziş
📄 README.md             ← RTL modülleri kılavuzu
📄 RTL_OVERVIEW.md       ← Proje yapısı haritası
📄 CERES_WRAPPER.md      ← SoC top module (282 L RTL)
📄 CPU_TOP_MODULE.md     ← CPU orchestration (698 L RTL)
📄 HAZARD_UNIT.md        ← Hazard detection (150 L RTL)

📁 stages/
  📄 FETCH_STAGE.md                (IF - 344 L RTL)
  📄 DECODE_STAGE.md               (ID - 1,808 L RTL)
  📄 EXECUTE_STAGE.md              (EX - 554 L RTL)
  📄 MEMORY_WRITEBACK_STAGES.md    (MEM/WB - 220 L RTL)
```

**Nasıl Kullanılır:**
1. Başlamak: `INDEX.md` açın
2. Hızlı referans: `README.md` kullanın
3. Detay: İlgili belgeyi açın
4. Kod: RTL dosyalarına bakın

---

## 🎓 Örnek Öğrenme Seansları

### Seans 1: Pipeline Tasarımı Öğreniyorum (90 min)

```
1. architecture.md (20 min)
   ├─ 5-stage pipeline
   └─ pipe1-4 registers
   
2. CPU_TOP_MODULE.md (50 min)
   ├─ Pipeline orchestration
   ├─ Data forwarding
   └─ Stall control
   
3. HAZARD_UNIT.md (20 min)
   └─ Hazard detection
```

### Seans 2: ADD Instruction'ı Takip Ediyorum (60 min)

```
1. DECODE_STAGE.md (20 min)
   └─ "Örnek: ADD x3, x1, x2"
   
2. EXECUTE_STAGE.md (20 min)
   └─ ALU ADD operation
   
3. MEMORY_WRITEBACK_STAGES.md (10 min)
   └─ WriteBack
   
4. Kod inspeksiyonu:
   rtl/core/stage02_decode/control_unit.sv
   rtl/core/stage03_execute/alu.sv
```

### Seans 3: Cache Miss Debug (60 min)

```
1. MEMORY_WRITEBACK_STAGES.md (20 min)
   └─ Memory operations
   
2. HAZARD_UNIT.md (15 min)
   └─ Stalling analysis
   
3. CPU_TOP_MODULE.md (15 min)
   └─ Pipeline timing
   
4. Waveform/trace inceleme
```

---

## 📚 Belgeler Özeti

| Belge | Konusu | Saat | Detay |
|-------|--------|------|-------|
| **INDEX.md** | Tüm belgeler | 10 min | Navigation hub |
| **README.md** | RTL modülleri | 20 min | Module map |
| **RTL_OVERVIEW.md** | Proje yapısı | 30 min | File structure |
| **CERES_WRAPPER.md** | SoC top | 45 min | Memory, CPU, peripherals |
| **CPU_TOP_MODULE.md** | Pipeline | 45 min | Orchestration, timing |
| **FETCH_STAGE.md** | IF stage | 45 min | PC, prediction, exceptions |
| **DECODE_STAGE.md** | ID stage | 45 min | Decode, registers, immediate |
| **EXECUTE_STAGE.md** | EX stage | 60 min | ALU, CSR, MUL/DIV |
| **MEMORY_WRITEBACK_STAGES.md** | MEM/WB | 45 min | Load/store, register write |
| **HAZARD_UNIT.md** | Hazards | 45 min | Forward, stall, flush |

---

## 🔗 Sık Kullanılan Linkler

**Başlangıç:**
- [RTL INDEX](./INDEX.md) - Tüm belgeler
- [RTL README](./README.md) - Modül guide

**Top Level:**
- [CERES_WRAPPER](./CERES_WRAPPER.md) - SoC
- [CPU_TOP_MODULE](./CPU_TOP_MODULE.md) - Pipeline

**Pipeline Stages:**
- [FETCH_STAGE](./stages/FETCH_STAGE.md) - IF
- [DECODE_STAGE](./stages/DECODE_STAGE.md) - ID
- [EXECUTE_STAGE](./stages/EXECUTE_STAGE.md) - EX
- [MEMORY_WRITEBACK](./stages/MEMORY_WRITEBACK_STAGES.md) - MEM/WB

**Support:**
- [HAZARD_UNIT](./HAZARD_UNIT.md) - Hazards

---

## ⌚ Zaman Tahmini

Konuya bağlı olarak:

| Hedef | Zaman | Kaynak |
|-------|-------|--------|
| Pipeline temellerini anla | 2 saat | PATH 2 |
| Tüm RTL'yi öğren | 6 saat | PATH 1 |
| Belirli modülü anla | 30-60 min | PATH 2 (specific) |
| Bug'ı hızlı bulma | 15-30 min | INDEX → modül → kod |
| Performance optimize | 1-2 saat | Timing analysis |

---

## 💡 İpuçları

### Verimli Okuma İçin:

1. **Hiyerarşi takip edin**: Başlangıç → İlgili → Detay
2. **Kod örneklerini inceleyin**: Anlaşılması için kritik
3. **Diyagramlar önemli**: ASCII diagrams çoğu şeyi açıklar
4. **Zamanı planla**: Aceleye getirmeyin, anla
5. **Alıştırma yap**: Sadece oku, mutlaka kod yaz

### Navigasyon İpuçları:

1. README.md'deki tabloları kullanın
2. Cross-references'i takip edin
3. "Sonraki Adımlar" bölümlerini okuyun
4. Belirsiz bölümleri yeniden okuyun
5. Kod ile karşılaştırın

### Kod İnceleme:

```bash
# Fetch stage bakımı:
cat /home/kerim/level-v/rtl/core/stage01_fetch/fetch.sv

# Decode stage:
cat /home/kerim/level-v/rtl/core/stage02_decode/control_unit.sv

# Execute stage:
cat /home/kerim/level-v/rtl/core/stage03_execute/alu.sv

# Hazard unit:
cat /home/kerim/level-v/rtl/core/hazard_unit.sv
```

---

## ❓ Sık Sorulan Sorular

**S: Nereden başlamalıyım?**
C: Bu sayfadaki durumunuza uygun PATH'i seçin

**S: Tüm belgeyi mi okumam gerek?**
C: Hayır - PATH 2 veya 3 seçin

**S: Bir modülü hızlı öğrenmek istiyorum**
C: README.md modül tablosunu kullanın

**S: Belirli bir sorunu çözmek istiyorum**
C: INDEX.md → Modül → Detay → Kod

**S: RTL kodunu nasıl bulurum?**
C: Belgeler dizini tanımlarını gösterir, sonra kodunu ararsınız

---

## 📞 Destek

Belgelerde sorun bulursanız:

1. İlgili belgenin "Sonraki Adımlar" bölümünü kontrol edin
2. INDEX.md veya README.md'deki tabloları kullanın
3. Cross-references'i takip edin
4. Aynı konudaki diğer belgeleri okuyun

---

## 🚀 İleri Adımlar

Temel RTL'yi anladıktan sonra:

1. **Compute Units** (Phase 2)
   - ALU deep dive
   - Multiplier/Divider
   - Branch Predictor

2. **Memory System** (Phase 3)
   - Cache architecture
   - TLB & PMA
   - CSR detailed

3. **Peripherals** (Phase 4)
   - UART integration
   - CLINT
   - GPIO/SPI/I2C

---

**Durumu**: Phase 1 Tamamlandı ✅  
**Sonraki**: Phase 2 - Compute Units  
**Tarafından oluşturuldu**: 1 Aralık 2025

**Başlamaya hazır mısınız?** → [INDEX.md](./INDEX.md) açın

