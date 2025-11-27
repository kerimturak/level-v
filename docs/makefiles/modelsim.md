Aşağıdaki döküman, **ModelSim/Questa (Intel/Starter Edition ile uyumlu)** `rules_modelsim.mk` dosyanız için profesyonel seviyede bir referanstır. Verilog/SystemVerilog derleme–koşum akışını standardize eder, log yönetimini düzenler ve GUI/Batch çalıştırmayı parametreleştirir. (Not: Intel/Starter Edition’da **`vopt` yoktur**; akış `vlog + vsim` ile çalışır.)

---

# 📘 ModelSim / Questa Makefile Dokümantasyonu

**Dosya:** `script/makefiles/rules_modelsim.mk`
**Amaç:** ModelSim/Questa derleme ve simülasyon akışını (GUI/Batch) otomatikleştirmek, log’ları düzenlemek ve CI’ye uygun hâle getirmek.

---

## 🧱 Genel Bakış

Bu Makefile şunları sağlar:

* **Derleme:** `vlog` ile RTL + testbench derlenir (work library).
* **Koşum:** `vsim` ile batch ya da GUI simülasyon.
* **Parametreleme:** CLI’dan `GUI`, `TEST`, `DO_FILE`, `SIM_TIME` vb. değiştirilebilir.
* **Log Yönetimi:** Zaman damgalı `vsim_*` log’ları; false-positive hata filtreleri.
* **Uyumluluk:** ModelSim **Intel/Starter** sürümü (vopt yok) + Linux/WSL/MSYS2.

---

## ⚙️ Konfigürasyon Değişkenleri

Ana Makefile veya `config.mk` içinde set edilir; bu dosya bu değişkenleri **kullanır**:

| Değişken          | Varsayılan                | Açıklama                                    |
| ----------------- | ------------------------- | ------------------------------------------- |
| `WORK_DIR`        | `work`                    | ModelSim çalışma kütüphanesi                |
| `INC_DIR`         | `./rtl/include`           | `\`include` dizinleri                       |
| `LOG_DIR`         | `./build/logs`            | Derleme/simülasyon log’ları                 |
| `TOP_LEVEL`       | *(zorunlu)*               | Testbench top modul adı (örn. `tb_wrapper`) |
| `SV_SOURCES`      | *(zorunlu)*               | RTL kaynak listesi                          |
| `TB_FILE`         | *(zorunlu)*               | Testbench dosyası                           |
| `SIM_DIR`         | `./sim`                   | `.do` script’lerinin olduğu klasör          |
| `SIM_TIME`        | `1us`                     | Batch modda koşum süresi                    |
| `BUILD_MODE_NAME` | `Debug`                   | Çıktılarda görünecek profil adı             |
| `GUI`             | `0`                       | `1` → GUI, `0` → batch                      |
| `TEST`            | `default_test`            | UVM test adı: `+UVM_TESTNAME=$(TEST)`       |
| `DO_FILE`         | `$(SIM_DIR)/do/questa.do` | GUI modunda çalışacak `.do`                 |

---

## 🔧 Araç Seçenekleri

### `vlog` (Derleyici)

Varsayılan `VLOG_OPTS` özet:

* `-sv` → SystemVerilog modu
* `-mfcu` → Çoklu dosyayı tek compilation unit olarak derle
* `+acc=npr` → Sinyal erişimi (debug/wave)
* `+incdir+$(INC_DIR)` → Include dizinleri
* `-svinputport=relaxed` → SV giriş portları esnekliği
* `-suppress vlog-2583 -suppress vlog-2275` → sık görülen zararsız uyarıları bastır

### `vsim` (Simülatör)

Varsayılan `VSIM_FLAGS` özet:

* `-t ns` → zaman birimi
* `-voptargs=+acc=npr` → (Starter’da vopt yok; burada `+acc` görünürlüğü için kullanılıyor)
* `+notimingchecks` → timing check kapatma (opsiyonel)

---

## 🧮 Hedefler (Targets)

### 1) `make compile` — Derleme

* `work/` kütüphanesini oluşturur.
* RTL + TB dosyalarını derler.
* Çıktı: `$(LOG_DIR)/compile.log`

**Başarı/Kayıp mantığı**

* Komutun gerçek **exit code**’u takip edilir.
* Log’taki “gerçek hata” satırları akıllı filtreyle taranır.
* “Errors: 0” yazan özet satırı **hata sayılmaz**.

### 2) `make simulate` — Simülasyon (Batch/GUI)

* **Batch (GUI=0):**

  * `vsim -c work.$(TOP_LEVEL) -do "run $(SIM_TIME); quit"`
  * Log: `$(LOG_DIR)/vsim_YYYYmmdd_HHMMSS.log`
  * Log’da sadece “** Error:” satırları hata sayılır; “Errors: 0” özet satırı **hata değildir**.
* **GUI (GUI=1):**

  * `vsim work.$(TOP_LEVEL) -do $(DO_FILE)`
  * GUI açılır; transcript dosyası default isimle aynı klasöre düşebilir.

**UVM Test Desteği:**
`make simulate TEST=my_test` → `+UVM_TESTNAME=my_test`

**DO Script Seçimi:**
`make simulate GUI=1 DO_FILE=sim/do/ddr.do`

**Süre Değiştirme:**
`make simulate SIM_TIME=20000ns`

### 3) `make rerun` — Hızlı yeniden koşum

* Derlemeyi atlar; mevcut `work/` ile koşar (Batch/GUI parametrelerine uyar).

### 4) Temizlik

* `make clean_modelsim` → `work/`, `transcript`, `vsim.wlf`, `modelsim.ini`, tüm log’lar silinir.
* `make clean_logs` → Sadece log’lar silinir; derlenmiş kütüphane kalır.

---

## 🧪 Kullanım Örnekleri

```bash
# Derle
make compile

# Batch modda simülasyon (varsayılan 1us)
make simulate

# Batch modda özel süre ve UVM testi
make simulate SIM_TIME=20000ns TEST=alu_random

# GUI modunda .do dosyası ile
make simulate GUI=1 DO_FILE=sim/do/questa.do

# Sadece logları temizle
make clean_logs

# Tam temizlik (work + loglar + transcript)
make clean_modelsim
```

---

## 🧠 Log Analizi Mantığı (False-Positive önleme)

* **Derleme:**

  * `EXIT_CODE != 0` → derleyici hatası (fail)
  * log’ta **“Error:”** geçen satırlar → hata kabul edilir
  * **“Errors: 0, Warnings: N”** → yalnızca özet satırı ⇒ **hata sayılmaz**

* **Simülasyon:**

  * `EXIT_CODE != 0` → simülatör hatası (fail)
  * log’ta **“** Error:”** (ModelSim gerçek hata formatı) varsa → hata
  * **“Errors: 0, Warnings: N”** → **hata sayılmaz**
  * İstersen “** Fatal:**” ve assertion kalıplarını da denetime ekleyebilirsin.

> İpucu: Genişletmek istersen küçük bir `script/utils/analyze_vsim_log.py` ile “Error/Fatal/Assertion” sayımlarını renkli özetleyip Makefile’dan çağırabilirsin.

---

## 🔍 Sık Karşılaşılan Uyarılar ve Anlamları

* `vsim-3015 [PCDPC] Port size ... does not match connection size ...`
  → **Port genişliği uyuşmazlığı**. Örn. `stall_i` 1-bit, bağlanan sinyal 3-bit.
  Çözüm: Port/sinyal bit genişliklerini hizala veya cast et.

* `vsim-PLI-3408 Too few data words read ... Expected N, found M`
  → **.mem init** dosyası beklenen satır sayısında değil.
  Çözüm: `.mem` dosyasını doğru kelime sayısıyla yeniden oluştur (örn. 8192 satır).

Bu tip uyarılar simülasyonu durdurmaz (Error: 0). Makefile bunları **hata saymaz**.

---

## 🧩 En İyi Pratikler

1. **`work/` ve log’ları** `.gitignore` ile versiyon kontrolünden çıkar.
2. Büyük tasarımlarda derleme hızını korumak için **`-mfcu`** kullan (zaten aktif).
3. Wave/debug için **`+acc=npr`** uygundur (signal erişimi).
4. CI’da:

   * `make compile` → `make simulate SIM_TIME=...`
   * Logları artefact olarak topla.
5. GUI testlerinde `.do` script’ini parametrele (`DO_FILE`) ve kontrolü script’e taşı.

---

## 🧩 Kısa Referans

### `vlog` sık kullanılanları

* `-sv` | SV modu
* `-mfcu` | Multi-file compile unit
* `+incdir+<dir>` | include dizini
* `+define+FOO=1` | makro
* `-work <lib>` | hedef kütüphane
* `-suppress <id>` | uyarı bastırma

### `vsim` sık kullanılanları

* `-c` | Batch mod
* `-do "<komutlar>"` | DO komutu satırı
* `-t ns` | zaman birimi
* `+UVM_TESTNAME=...` | UVM test seçimi
* `-coverage` | (tam lisanslarda) coverage
* `-l <file>` | transcript log yolu

---

## 🧷 Sorun Giderme

* **`work` yok**: `make compile` `vlib work` üretir; yetki/dizin sorunlarını kontrol et.
* **GUI açılıyor ama design load edilmedi**: `TOP_LEVEL` doğru mu, `vlog` hatasız mı?
* **“Error” false positive**: Log filtresi “** Error:” kalıbını arar; “Errors: 0” dışarıda bırakılmıştır.
* **MEM uyarıları**: `.mem` satır sayısı/formatını düzelt (ör. satır başına 32-bit hex).

---

## ✅ Özet

| Hedef            | Amaç                               |
| ---------------- | ---------------------------------- |
| `compile`        | RTL + TB derleme (work lib)        |
| `simulate`       | Batch/GUI simülasyon               |
| `rerun`          | Yeniden koşum (derlemesiz)         |
| `clean_logs`     | Sadece logları temizle             |
| `clean_modelsim` | Tüm ModelSim artefact’ları temizle |

Bu dokümanı repo’ya `docs/modelsim-makefile.md` olarak koyabilir ve ekip içi standardınızın parçası yapabilirsiniz. İstersen aynı formatta **PDF sürüm** de hazırlayabilirim.
