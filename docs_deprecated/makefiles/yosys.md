Harika kanka 💎
Aşağıda **“Yosys Makefile Dokümantasyonu”** tam sürümünü hazırladım.
Bu belgeyi `docs/makefile_yosys.md` veya `script/docs/makefile_yosys.md` altına koyabilirsin.
Tüm kurallar (check / synth / show / clean) açıklamalarıyla birlikte var.
Ayrıca her aşamada üretilen log, netlist ve görsel dosyalar tablo halinde verilmiş.

---

# 🧩 **YOSYS Makefile Dökümantasyonu**

## 📘 Amaç

Bu Makefile, **Yosys Open SYnthesis Suite** aracını kullanarak RTL tasarımlar üzerinde
statik analiz, sentezleme ve görselleştirme işlemlerini otomatikleştirir.

Yosys sayesinde:

* RTL kodundaki **yapısal hatalar** (loop, multiple driver, unconnected nets) yakalanabilir.
* RTL, gate-level netliste dönüştürülüp analiz edilebilir.
* Tasarımın **görsel bağlantı diyagramı (graph)** SVG formatında üretilebilir.

---

## ⚙️ Genel Yapı

| Kural         | Açıklama                                             | Çıktı Dosyaları                                  |
| ------------- | ---------------------------------------------------- | ------------------------------------------------ |
| `yosys_check` | Statik yapısal kontrol — RTL bütünlüğü test edilir   | `yosys_check.log`                                |
| `yosys_synth` | RTL sentezlenir, netlist (Verilog + JSON) üretilir   | `_netlist.v`, `_netlist.json`, `yosys_synth.log` |
| `yosys_show`  | Sentezlenmiş yapının grafiksel diyagramı oluşturulur | `_graph.svg`, `yosys_show.log`                   |
| `clean_yosys` | Tüm rapor, netlist ve grafik dosyalarını temizler    | —                                                |

---

## 🧠 **1. Yosys Structural Check (`yosys_check`)**

Yapısal analiz komutu:

```bash
make yosys_check
```

### 🔍 Ne yapar?

* `read_verilog -sv` ile RTL dosyalarını okur
* `hierarchy -check -top` ile hiyerarşi bütünlüğünü kontrol eder
* `proc; opt; check` ile optimizasyon sonrası **loop**, **driver** ve **unconnected** kontrollerini yapar

### ✅ Kontrol Edilen Hatalar

| Tür                    | Açıklama                               |
| ---------------------- | -------------------------------------- |
| **Combinational loop** | Döngüsel bağlı sinyaller               |
| **Multiple driver**    | Aynı sinyali süren birden fazla kaynak |
| **Unconnected nets**   | Bağlantısı olmayan port veya sinyaller |

### 🧾 Log Örneği

```
[RUNNING YOSYS STRUCTURAL CHECKS — Debug]
Checking module top...
Warning: Wire 'inst_data' has no driver.
ERROR: Found combinational loop between 'alu_op' and 'alu_res'.
❌ Combinational loop(s) detected!
```

### 📁 Üretilen Dosya

| Dosya                           | Açıklama              |
| ------------------------------- | --------------------- |
| `build/reports/yosys_check.log` | Detaylı analiz raporu |

---

## 🧱 **2. Yosys Synthesis (`yosys_synth`)**

RTL → gate-level netlist üretimi:

```bash
make yosys_synth
```

### 🔍 Ne yapar?

* Tasarımı `read_verilog -sv` ile okur
* `synth -top $(TOP_LEVEL)` komutuyla sentezler
* Çıktıları hem **Verilog** hem **JSON** formatında yazar

### ⚠️ Otomatik Hata Yakalama

* `grep -qi "ERROR:"` ile Yosys log’u taranır.
* Parse veya sentez hataları varsa `make` otomatik olarak başarısız olur (`exit 1`).

### 📁 Üretilen Dosyalar

| Dosya                              | Açıklama                                            |
| ---------------------------------- | --------------------------------------------------- |
| `build/reports/yosys_synth.log`    | Sentez log’u                                        |
| `build/reports/<top>_netlist.v`    | Gate-level netlist (Verilog formatında)             |
| `build/reports/<top>_netlist.json` | Netlistin JSON temsili (EDA araçlarıyla okunabilir) |

### 🧩 Örnek Komut Dizisi

```bash
yosys -p "read_verilog -sv rtl/core/*.sv;
          hierarchy -top cpu;
          synth -top cpu;
          write_verilog build/reports/cpu_netlist.v"
```

---

## 🖼️ **3. Yosys Visualization (`yosys_show`)**

Grafiksel netlist görünümü:

```bash
make yosys_show
```

### 🔍 Ne yapar?

* RTL’i sentezler
* `show -format svg -prefix build/reports/<top>_graph` komutu ile netlisti çizdirir
* Çıktıyı `.svg` olarak kaydeder
* Görüntüyü otomatik olarak **Graphviz tabanlı** olarak oluşturur

### 🌐 Görüntüleme

| Komut                                  | Açıklama                   |
| -------------------------------------- | -------------------------- |
| `xdg-open build/reports/cpu_graph.svg` | (Linux) SVG dosyasını aç   |
| `start build/reports/cpu_graph.svg`    | (Windows) SVG dosyasını aç |

### 📁 Üretilen Dosyalar

| Dosya                           | Açıklama                |
| ------------------------------- | ----------------------- |
| `build/reports/yosys_show.log`  | Görselleştirme logu     |
| `build/reports/<top>_graph.svg` | Netlistin SVG diyagramı |

### 🧩 Görselde Neler Görülür

| Eleman                     | Açıklama                                          |
| -------------------------- | ------------------------------------------------- |
| 🔵 **Ports**               | Giriş/çıkış pinleri (Input: solda, Output: sağda) |
| 🟢 **Modules**             | Alt modüller kutu olarak gösterilir               |
| 🔴 **Wires / Nets**        | Bağlantı hatları                                  |
| 🟡 **Registers / Latches** | Sentezlenmiş register yapıları                    |
| ⚫ **Operators**            | Mantıksal işlemler (and/or/xor, mux)              |

### 🎨 Örnek Komut

```bash
yosys -p "read_verilog -sv rtl/core/alu.sv;
          synth -top alu;
          show -format svg -prefix build/reports/alu_graph"
```

---

## 🧹 **4. Temizlik (`clean_yosys`)**

Tüm Yosys log, netlist ve görselleri temizler:

```bash
make clean_yosys
```

### Silinen Dosyalar

```
build/reports/yosys_check.log
build/reports/yosys_synth.log
build/reports/yosys_show.log
build/reports/<top>_netlist.v
build/reports/<top>_netlist.json
build/reports/<top>_graph.svg
```

---

## 🧰 **Yosys Komut Özeti**

| Komut                         | Açıklama                                    |
| ----------------------------- | ------------------------------------------- |
| `read_verilog -sv <files>`    | Verilog/SystemVerilog dosyalarını okur      |
| `hierarchy -check -top <top>` | Top module’ü tanımlar ve hiyerarşi doğrular |
| `proc`                        | Always bloklarını işlem ağacına dönüştürür  |
| `opt`                         | Gereksiz netleri optimize eder              |
| `check`                       | Yapısal hataları kontrol eder               |
| `synth -top <top>`            | RTL → gate-level dönüşümü                   |
| `write_verilog`               | Sentez sonrası netlisti kaydeder            |
| `show -format svg`            | Görsel diyagram oluşturur (Graphviz)        |

---

## 📊 **Otomatik Hata Yakalama Mantığı**

Her `make` kuralı, Yosys’in **log içeriğini** ve **exit code’unu** kontrol eder:

```bash
if grep -qi "ERROR:" <logfile>; then
    echo "❌ Hata bulundu!"
    exit 1
fi
```

Böylece CI/CD ortamlarında hatalı sentez veya loop tespiti durumunda pipeline otomatik olarak durur.

---

## 🔮 Geliştirme Fikirleri

| Fikir                | Açıklama                                                          |
| -------------------- | ----------------------------------------------------------------- |
| `yosys_stat`         | `stat -json > stat.json` ile kaynak kullanımı raporu üretilebilir |
| `yosys_timing`       | `tee -a timing.log` ile yol gecikme analizi yapılabilir           |
| `yosys_graph_png`    | `.dot`’tan PNG üretimi: `dot -Tpng -O <file>.dot`                 |
| `yosys_partial_show` | `select module_name; show` ile alt modül görselleştirmesi         |

---

## 🧩 Entegre Kullanım

```bash
# 1️⃣ Yapısal analiz
make yosys_check

# 2️⃣ Sentezleme ve netlist üretimi
make yosys_synth

# 3️⃣ Grafiksel netlist görünümü
make yosys_show
xdg-open build/reports/cpu_graph.svg

# 4️⃣ Temizlik
make clean_yosys
```

---

## 📁 Önerilen Klasör Yapısı

```
project/
 ├─ rtl/
 │   ├─ core/
 │   └─ pkg/
 ├─ sim/
 ├─ build/
 │   └─ reports/
 └─ script/
     └─ makefiles/
         └─ rules_yosys.mk
```

---

## ✅ Sonuç

Bu Yosys Makefile altyapısı ile:

* Otomatik statik kontrol,
* Netlist üretimi,
* Görselleştirme,
* CI/CD dostu hata yönetimi
  bir arada ve **tam entegre** şekilde çalışır.

---

İstersen bu dokümanı PDF olarak “**Yosys Structural Flow — CERES Edition**” başlığıyla
`docs/` altına otomatik olarak dönüştürecek `make doc_yosys` kuralı da ekleyebilirim (pandoc veya pypandoc ile).
Ekleyeyim mi o da?
