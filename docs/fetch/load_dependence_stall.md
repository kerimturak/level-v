Harika soru Kerim 👏
Bu sorunun arkasında **pipeline veri bağımlılığı (data dependency)** yönetiminin en kritik noktalarından biri yatıyor — özellikle **load-use hazard (yükleme-kullanma bağımlılığı)** durumunda.

Aşağıda neden **fetch aşamasının stall edilmesi gerektiğini** adım adım, pipeline akışını referans alarak açıklayayım 👇

---

## 🧠 1. Temel Durum: Load-Use Dependency Nedir?

Örnek:

```assembly
lw   x3, 0(x5)     // memory’den x3’e veri yükleniyor
add  x4, x3, x6    // hemen sonraki cycle’da x3 kullanılmak isteniyor
```

Burada `add` talimatı, bir önceki `lw`’in **henüz tamamlanmamış** sonucuna ihtiyaç duyuyor.
Ancak load verisi **memory stage** (örneğin 4. aşama) bitmeden hazır değil.

---

## 🏗️ 2. Pipeline’da Olanlar (5 aşamalı örnek)

| Stage | lw (önceki)  | add (sonraki)             |
| ----- | ------------ | ------------------------- |
| IF    | lw fetch     | add fetch                 |
| ID    | lw decode    | add decode                |
| EX    | lw addr calc | add execute (x3 lazım!) ❌ |
| MEM   | lw mem read  | -                         |
| WB    | lw writeback | -                         |

Gördüğün gibi `add` talimatı EX aşamasında operandları okumaya çalışırken,
`lw`’in verisi henüz memory’den dönmemiş durumda.

Buna **load-use hazard** (ya da “RAW hazard”) denir.

---

## ⚙️ 3. Forwarding Yeterli Değilse Ne Olur?

Forwarding mekanizması genellikle ALU sonuçlarını EX veya MEM aşamasından
erken ileterek (bypass) çözer.

Ama `lw` durumunda veri **memory’den** geldiği için, forwarding **en erken MEM sonunda** mümkündür.
Yani `add` talimatının EX aşamasına **bir cycle erken** girmesi hatalı olur.

Bunu çözmenin iki yolu vardır:

* **(a)** ID aşamasında `load-use` bağımlılığı tespit edilip **1 cycle stall** eklenir.
* **(b)** Daha karmaşık bir **hazard detection + forwarding** mekanizması varsa dinamik olarak çözülür.

Senin basit OoO olmayan 5 aşamalı işlemcinde genellikle (a) uygulanır:
→ `lw` sonrası bir talimat hemen aynı register’ı kullanıyorsa, **IF ve ID aşamaları stall edilir.**

---

## ⛓️ 4. Fetch Neden Stall Ediliyor?

Bu nokta önemli:
**Fetch aşaması**, pipeline’ın en başıdır. Eğer decode veya execute aşaması stall olursa,
fetch’in çalışmaya devam etmesi **yeni talimatları pipeline’a “taşırır”**,
ve bu da *pipeline bubble*’ı kontrolsüz hale getirir (yani flush karmaşası doğar).

Dolayısıyla, hazard detection bir “global stall” sinyali üretir (`stall_i` gibi).
Bu sinyal genellikle şunları durdurur:

* **IF/ID register** (fetch çıktısının decode’a geçmesi)
* **PC ilerlemesi (pc_en = 0)**
* **Fetch request valid** (align_buffer’a yeni istek atılmaz)

Yani load-use hazard tespit edilirse:

```verilog
pc_en = 0;
fetch_valid = 0;
```

Bu sayede **fetch aşaması “freeze” edilir**, pipeline yeni talimat getirmez,
ve bir cycle sonra hazard ortadan kalktığında normal akış devam eder.

---

## 🧩 5. Örnek Mantık (Hazard Unit içinde)

```systemverilog
// decode stage'de tespit edilen hazard
logic load_use_hazard = id_ex_mem_read &&
                        ((id_ex_rd == if_id_rs1) || (id_ex_rd == if_id_rs2));

assign stall_if = load_use_hazard;
assign stall_id = load_use_hazard;
assign flush_ex = load_use_hazard; // bubble insert
```

Bu durumda:

* `stall_if` → fetch aşaması durur
* `stall_id` → decode aşaması durur
* `flush_ex` → EX aşamasına bubble gider

---

## 🚀 6. Özet Akış

| Aşama                                           | Ne olur?                 |
| ----------------------------------------------- | ------------------------ |
| Load talimatı MEM’den veri bekliyor             | Sonuç henüz yazılmadı    |
| Sonraki talimat aynı register’a ihtiyaç duyuyor | Dependency tespit edildi |
| Hazard unit `stall` üretiyor                    | IF ve ID donuyor         |
| PC ilerlemiyor                                  | Yeni fetch yapılmıyor    |
| 1 cycle sonra load sonucu hazır                 | Fetch yeniden başlıyor   |

---

## 🎯 Sonuç

Fetch aşaması **direkt olarak load-use dependency’nin kurbanı değildir**,
ama **pipeline bütünlüğünü korumak için stall zincirinin bir parçası olur**.

> 🔹 Eğer fetch durdurulmazsa → decode’da tıkanıklık oluşur → pipeline kayar → yanlış talimatlar fetch edilir.
> 🔹 Eğer fetch durdurulursa → tüm aşamalar senkron kalır → bubble doğru yere eklenir.

---

İstersen bir sonraki adımda senin `stall_i[4:0]` yapına uygun bir **hazard detection unit** (verilog modülü) örneği hazırlayayım — load-use, branch mispredict ve exception’ları da kapsayacak şekilde.
İster misin onu da birlikte yazalım?
