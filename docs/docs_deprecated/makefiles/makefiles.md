Mükemmel hareket Kerim 💯
Artık elindeki sistem gerçekten profesyonel bir seviyede — ama bunu sürdürülebilir kılan şey, **iyi belgelenmiş bir build dokümantasyonu**.

Aşağıda sana adım adım açıklamalı bir **“CERES Build System v2 — Technical Documentation”** hazırladım.
Bu belgeyi doğrudan `docs/build_system.md` gibi bir yere koyabiliriz (veya README’nin altına da ekleyebilirsin).

---

# 🧠 CERES Build System v2 — Documentation

## 📘 Genel Bakış

**CERES Build System v2**, RISC-V işlemci projeleri için hazırlanmış,
**profil destekli (debug/release/test)**, **modüler**, **platform bağımsız**
ve **profesyonel EDA akışlarına uygun** bir Makefile yapısıdır.

Amaç:

* RTL ve testbench derlemelerini **tek merkezden** yönetmek,
* Farklı araçların (ModelSim, Verilator, Yosys) görevlerini **ayrı modüller** halinde tutmak,
* Build dosyalarını, logları ve raporları **tek bir `build/`** klasörü altında toplamak,
* Linux ve Windows sistemlerde **sorunsuz çalışan**,
* Okunabilir, sürdürülebilir ve genişletilebilir bir build altyapısı sağlamaktır.

---

## 🏗️ Genel Mimari

```
ceres-riscv/
├── Makefile                        ← Ana kontrol dosyası
├── script/
│   ├── config.mk                   ← Global değişkenler ve dizin ayarları
│   ├── profiles.mk                 ← Build profilleri (debug/release/test)
│   └── makefiles/                  ← Araç bazlı alt makefile’lar
│       ├── rules_modelsim.mk       ← ModelSim / Questa akışı
│       ├── rules_verilator.mk      ← Verilator lint ve simülasyon
│       ├── rules_yosys.mk          ← Yosys statik analiz
│       └── rules_clean.mk          ← Temizlik kuralları
└── build/
    ├── work/                       ← ModelSim çalışma kütüphanesi
    ├── obj_dir/                    ← Verilator derleme çıktıları
    ├── logs/                       ← Tüm log dosyaları
    └── reports/                    ← Statik analiz ve raporlar
```

---

## ⚙️ 1. `script/config.mk` — Temel Ortam ve Dizin Ayarları

Bu dosya sistemin temel yapı taşlarını tanımlar:

| Değişken                                       | Açıklama                                                      |
| ---------------------------------------------- | ------------------------------------------------------------- |
| `ROOT_DIR`                                     | Proje kök dizini (otomatik olarak algılanır).                 |
| `RTL_DIR`                                      | RTL kaynak dosyalarının bulunduğu dizin (`rtl/`).             |
| `SIM_DIR`                                      | Simülasyon dosyaları (`sim/tb`, `sim/do`, `sim/cpp`).         |
| `BUILD_DIR`                                    | Tüm geçici dosyaların toplandığı kök dizin (`build/`).        |
| `WORK_DIR`, `OBJ_DIR`, `LOG_DIR`, `REPORT_DIR` | Araç bazlı alt dizinler.                                      |
| `INC_DIR`                                      | RTL include dosyalarının dizini (`rtl/include/`).             |
| `TB_FILE`                                      | Ana testbench dosyası (`tb_wrapper.sv`).                      |
| `TOP_LEVEL`                                    | Simülasyonun top modülü ismi.                                 |
| `SIM_TIME`                                     | ModelSim’de çalıştırılacak simülasyon süresi.                 |
| `PLATFORM`                                     | Linux veya Windows ortamını otomatik algılar.                 |
| `VLIB`, `VLOG`, `VSIM`, `VERILATOR`, `YOSYS`   | Kullanılan araçların komut adları.                            |
| `MODE`                                         | Build modu (`debug`, `release`, `test`). Varsayılan: `debug`. |
| `DEFINE_MACROS`                                | Derleme sırasında verilmesi gereken `+define+` parametreleri. |

💡 Bu dosya, tüm Makefile’lar tarafından include edilir.
Yani global ortam değişkenlerinin tek kaynağıdır.

---

## 🧩 2. `script/profiles.mk` — Build Profilleri

Bu dosya, projeyi farklı **derleme modlarında (profile)** çalıştırmak için kullanılır.

| Profil      | Tanım                                                                               | Tipik Kullanım                 |
| ----------- | ----------------------------------------------------------------------------------- | ------------------------------ |
| **debug**   | Geliştirme ve hata ayıklama modu. Tüm sinyaller dump edilir, assertion’lar açıktır. | `make simulate_gui MODE=debug` |
| **release** | Optimizasyon odaklı mod. Log’lar kısaltılır, build süresi düşürülür.                | `make verilate MODE=release`   |
| **test**    | RISC-V ISA testleri veya regression suite çalıştırmak için optimize edilmiş mod.    | `make yosys_check MODE=test`   |

### Profillerin Etkileri:

| Değişken           | Açıklama                                                                   |
| ------------------ | -------------------------------------------------------------------------- |
| `BUILD_MODE_NAME`  | Konsol çıktısında gösterilen mod ismi.                                     |
| `DEFINE_MACROS`    | Mode’a özel tanımlar (`+define+DEBUG`, `+define+TEST_ENV`, vb.).           |
| `VLOG_FLAGS_EXTRA` | Mode’a özel ek `+define+` veya flag parametreleri.                         |
| `OPT_LEVEL`        | C++ derlemelerinde kullanılacak optimizasyon seviyesi (`-O0`, `-O2`, vs.). |
| `BUILD_DESC`       | Konsola yazılan açıklama (örneğin “🚀 Release mode enabled…”).             |

---

## 💻 3. `script/makefiles/` Altındaki Araç Bazlı Kurallar

Her alt Makefile, **tek bir EDA aracını** veya görev grubunu yönetir.
Bu sayede sistem modüler ve bakım kolay olur.

---

### 🔹 `rules_modelsim.mk` — ModelSim / Questa Akışı

İçerdiği hedefler:

| Hedef          | Açıklama                                                 |
| -------------- | -------------------------------------------------------- |
| `compile`      | Tüm RTL kaynaklarını ve testbench’i derler.              |
| `simulate`     | Batch modda (`-c`) simülasyon çalıştırır.                |
| `simulate_gui` | GUI modunda QuestaSim’i açar (`questa.do` script’i ile). |

Kullanımı:

```bash
make compile
make simulate MODE=debug
make simulate_gui MODE=release
```

---

### 🔹 `rules_verilator.mk` — Verilator Akışı

İçerdiği hedefler:

| Hedef           | Açıklama                                                       |
| --------------- | -------------------------------------------------------------- |
| `lint`          | Verilator ile statik kontrol (combinational loop, latch, vs.). |
| `verilate`      | Verilator C++ modelini derler (`--cc`, `--build`).             |
| `run_verilator` | C++ modelini çalıştırır (`obj_dir/V<top>`).                    |

Kullanımı:

```bash
make lint
make verilate MODE=release
make run_verilator
```

---

### 🔹 `rules_yosys.mk` — Yosys Statik Kontrol

| Hedef         | Açıklama                                                                               |
| ------------- | -------------------------------------------------------------------------------------- |
| `yosys_check` | Yapısal tutarlılık kontrolü (`unconnected nets`, `loops`, `multi-drivers`, vs.) yapar. |

Kullanımı:

```bash
make yosys_check
```

---

### 🔹 `rules_clean.mk` — Temizlik

| Hedef   | Açıklama                               |
| ------- | -------------------------------------- |
| `clean` | Tüm geçici dosyaları (`build/`) siler. |

Kullanımı:

```bash
make clean
```

---

## 🧠 4. Ana `Makefile`

Ana dosya yalnızca **koordinasyon** görevini üstlenir.

* Ortak dosyaları (`config.mk`, `profiles.mk`) include eder.
* Araç bazlı makefile’ları (`rules_*.mk`) yükler.
* `help` menüsünü ve varsayılan hedefi (`simulate_gui`) tanımlar.

### Örnek Kullanım

```bash
make                      # Varsayılan: GUI simülasyonu (debug mode)
make simulate_gui MODE=release
make verilate MODE=release
make yosys_check MODE=test
make clean
```

---

## 🧩 5. Build Akışı Örneği

```mermaid
flowchart TD
    A[Start] --> B[make simulate_gui MODE=debug]
    B --> C[compile]
    C --> D[work library oluştur]
    D --> E[VLOG ile derleme]
    E --> F[VSIM GUI açılır]
    F --> G[Simülasyon run $(SIM_TIME)]
    G --> H[Log dosyaları build/logs altına kaydedilir]
    H --> I[Simulation complete]
```

---

## 📊 6. Log & Output Düzeni

| Klasör           | İçerik                                                                             |
| ---------------- | ---------------------------------------------------------------------------------- |
| `build/work/`    | ModelSim çalışma kütüphanesi (`work/`).                                            |
| `build/obj_dir/` | Verilator tarafından üretilen C++ dosyaları.                                       |
| `build/logs/`    | Tüm araçların logları (`compile.log`, `sim_batch.log`, `verilator_lint.log`, vb.). |
| `build/reports/` | Yosys veya synthesis sonrası raporlar.                                             |

Bu sayede **tüm geçici dosyalar merkezi bir yerde** tutulur.

---

## 🔥 7. İleri Seviye Kullanım Fikirleri

| Özellik                 | Açıklama                                                                             |
| ----------------------- | ------------------------------------------------------------------------------------ |
| **Parallel Build**      | `make -j$(nproc)` ile multi-core derleme.                                            |
| **Incremental Compile** | Gelecekte `.stamp` veya `make depend` mekanizması eklenebilir.                       |
| **Auto Versioning**     | `$(shell git rev-parse --short HEAD)` ile build loglarına commit eklenebilir.        |
| **Coverage Target**     | `make coverage MODE=test` eklenerek UVM/Verilator coverage ölçümü yapılabilir.       |
| **RISCV Tests**         | `make riscv_tests` eklenip `riscv-tests` veya `benchmarks` akışı entegre edilebilir. |

---

## 🧩 8. Kısaca Akış Mantığı

1. **Ana Makefile** sadece hedefleri yönlendirir.
2. **config.mk** ortamı hazırlar.
3. **profiles.mk** build tipini belirler.
4. **rules_*.mk** her araç için işlemi yürütür.
5. **Sonuçlar build/ altında toplanır.**

---

## ✅ 9. Örnek Kullanım Senaryoları

### 🔹 Geliştirme Aşaması

```bash
make simulate_gui MODE=debug
```

> Debug mode aktif, waveform ve assertion açık.

### 🔹 Performans Testi

```bash
make verilate MODE=release
./build/obj_dir/Vtb_wrapper
```

> Release mode, optimize edilmiş C++ model.

### 🔹 ISA Testleri

```bash
make yosys_check MODE=test
```

> Test environment, özel tanımlar + structural kontrol.

### 🔹 Temizlik

```bash
make clean
```

> Tüm geçici dosyalar silinir (`build/` tamamen temizlenir).

---

## 🧩 10. Sürüm Bilgisi

**CERES Build System v2**
Author: *Kerim Turak*
Purpose: *Professional modular build environment for RISC-V CPU projects*
Compatible: *ModelSim / Questa / Verilator / Yosys (Linux + Windows)*

---

İstersen bu dokümantasyonu `.md` formatında tam olarak oluşturayım
(`docs/build_system.md`) ve Hugo’da bloga veya GitHub README’ne eklenebilir hale getireyim.
Hazır markdown versiyonunu oluşturayım mı?
