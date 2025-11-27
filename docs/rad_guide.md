Elbette! İşte 5 aşamalı bir RISC-V işlemcide **RAS (Return Address Stack)** konusunu derinlemesine ve uygulamalı olarak açıklayan kapsamlı bir Markdown rehberi:

---

# 🧠 RAS (Return Address Stack) – Derinlemesine Rehber

> **ceres İşlemci Tasarımı – Gshare Branch Predictor + RAS Destekli**

---

## 📌 İçindekiler

1. [RAS Nedir?](#ras-nedir)
2. [RAS Ne Zaman Kullanılır?](#ras-ne-zaman-kullanılır)
3. [RAS İşlemleri: Push, Pop, Restore](#ras-i̇şlemleri-push-pop-restore)
4. [5 Aşamalı Pipeline'da RAS Etkisi](#5-aşamalı-pipeline-da-ras-etkisi)
5. [Neden Restore Yapılır?](#neden-restore-yapılır)
6. [RAS Restore Senaryoları](#ras-restore-senaryoları)
7. [RAS + Gshare Entegrasyonu (ceres Örneği)](#ras--gshare-entegrasyonu-ceres-örneği)
8. [Performans Gözlemi ve İstatistikler](#performans-gözlemi-ve-i̇statistikler)
9. [Gelişmiş Yöntemler](#gelişmiş-yöntemler-shadow-ras-vb)

---

## 🧩 RAS Nedir?

**RAS (Return Address Stack)**, fonksiyon çağrılarında (`jal`, `call`) dönüş adresini saklayan özel bir stack yapısıdır.  
Amaç: `ret` veya `jalr` gibi komutlar geldiğinde doğru dönüş adresine gitmek.

🟢 **Küçük bir LIFO (Last-In-First-Out) yapısıdır.**

```text
jal func1       -->  push(pc + 4)
jal func2       -->  push(pc + 4)
ret             -->  pop() --> jump to saved return address
```

---

## ⛳ RAS Ne Zaman Kullanılır?

| Talimat  | RAS İşlemi | Açıklama                                 |
|----------|------------|-------------------------------------------|
| `jal`    | push       | Dönüş adresini RAS'a ekler (`pc+4`)       |
| `ret`    | pop        | RAS'tan adres çıkarır ve oraya atlar      |
| `jalr`   | pop/push   | Hem push hem pop gerekebilir (Uygulamaya göre) |

> Not: `rd = x1 (ra)` ve `rs1 = x1` gibi register analizleriyle karar verilir.

---

## 🔁 RAS İşlemleri: Push, Pop, Restore

- 🟩 **Push:** Yeni bir dönüş adresi stack’in en üstüne eklenir.
- 🟥 **Pop:** Stack’in en üstündeki adres çıkarılır (ve tahmin olarak kullanılır).
- 🟨 **Restore:** Yanlış yapılan push/pop işlemleri geri alınır.

---

## ⚙️ 5 Aşamalı Pipeline'da RAS Etkisi

| Aşama | Açıklama                                           | RAS İlgisi |
|-------|----------------------------------------------------|------------|
| IF    | Tahminle fetch yapılır (RAS’tan gelen adresle)     | ✅         |
| ID    | `jal`, `ret`, `jalr` gibi komutlar ayrıştırılır    | ✅         |
| EX    | Branch/jump kararı burada netleşir                 | ✅         |
| MEM   | Bellek erişimi                                     | ❌         |
| WB    | Sonucun yazılması                                  | ❌         |

> ✅ RAS restore işlemi yapılırken **IF, ID, EX** aşamaları flush edilir.

---

## ❓ Neden Restore Yapılır?

1. **Speculative execution** sırasında yapılan `push` veya `pop` işlemi yanlış olabilir.
2. `jal` çağrısı tahmin edilmiş ama aslında yürütülmemiş olabilir.
3. `ret` komutu pop yaptı ama speculative imiş → geri alınmalı.
4. Branch tahmini hatalıysa, speculative RAS işlemleri geçersizdir.

---

## 🚨 RAS Restore Senaryoları

### 1. `jal` spekülatifti → Flush edilince push geri alınmalı
### 2. `ret` spekülatifti → Pop işlemi yanlış → restore yapılmalı
### 3. Nested call: sadece alt seviye speculatif → tek push geri alınmalı
### 4. BTB `ret` sandı ama aslında değil → RAS yanlış pop etti

> 🎯 Restore işlemi genellikle `restore_pc_i` kullanarak gerçekleştirilir.

---

## 🔧 RAS + Gshare Entegrasyonu (ceres Örneği)

```systemverilog
ras #(.RAS_SIZE(RAS_SIZE)) ras (
  .clk_i(clk_i),
  .rst_ni(rst_ni),
  .restore_i(restore_ras),
  .restore_pc_i(stage_pc[0]),
  .req_valid_i(valid_if_jal_or_jalr),
  .rd_addr_i(inst_i.rd_addr),
  .r1_addr_i(inst_i.r1_addr),
  .j_type_i(j_type),
  .jr_type_i(jr_type),
  .return_addr_i(is_comp_i ? pc2_i : pc4_i),
  .popped_addr_o(popped_addr),
  .predict_valid_o(ras_taken)
);
```

- `restore_i` = Tahmin yanlışsa aktive edilir.
- `return_addr_i` = `jal` sonrası push edilecek adres.
- `popped_addr_o` = `ret` tahmini için adres.

---

## 📊 Performans Gözlemi ve İstatistikler

```systemverilog
logic [31:0] per_ras_count_predict_hit;
logic [31:0] per_ras_count_predict_miss;

always_ff @(posedge clk_i) begin
  if (!rst_ni) begin
    per_ras_count_predict_hit  <= 0;
    per_ras_count_predict_miss <= 0;
  end else if (!stall_i && ras_taken_q[1]) begin
    if (!spec_hit_i)
      per_ras_count_predict_miss <= per_ras_count_predict_miss + 1;
    else
      per_ras_count_predict_hit  <= per_ras_count_predict_hit + 1;
  end
end
```

---

## 🚀 Gelişmiş Yöntemler (Shadow RAS vb.)

### 1. **Checkpoint-based RAS**
- Her speculative push sonrası checkpoint alınır
- Flush sonrası checkpoint’e geri dönülür

### 2. **Shadow RAS**
- İki RAS: biri speculative, biri non-speculative
- Commit aşamasında speculative RAS devreye alınır

### 3. **Speculative bit işaretleme**
- Her RAS entry için valid + speculative bit tutmak

---

## 📌 Özet

| Durum                        | Yapılacak İşlem      |
|-----------------------------|-----------------------|
| `jal` yanlış tahmin         | Push geri alınmalı    |
| `ret` yanlış tahmin         | Pop geri alınmalı     |
| Branch yanlış tahmin        | IF-ID-EX flush, RAS restore |
| Nested speculative call     | Sadece alt seviye restore |
| BTB `ret` sandı ama değil   | RAS’tan yanlış pop → restore |

---

## ✨ Ekstra: Test Durumu

```verilog
initial begin
  // jal x1, func  --> push pc+4
  // func: ret     --> pop
  // bne x3, x0, fail  --> misprediction!
  // restore expected
end
```

---

Eğer bu dokümantasyonu GitHub projenin README veya `docs/` klasörüne koymak istersen, sana markdown dosyası olarak da export edebilirim.

Devamında bu yapının testbenchi, assertion’ları veya verilere dayalı analizleriyle ilerlemek ister misin?