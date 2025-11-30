# CERES RISC-V Test Configuration System

Bu dizin, test konfigürasyonlarını merkezi olarak yönetmek için JSON tabanlı bir sistem sağlar.

## 📁 Dizin Yapısı

```
script/config/tests/
├── tests.schema.json    # JSON şema validasyonu
├── default.json         # Varsayılan ayarlar (tüm testler miras alır)
├── isa.json            # riscv-tests ISA testleri
├── arch.json           # riscv-arch-test compliance testleri
├── imperas.json        # Imperas RISC-V testleri
├── bench.json          # Benchmark testleri
├── coremark.json       # CoreMark benchmark
├── csr.json            # Machine CSR testleri
├── custom.json         # Kustom UART testleri (kullanıcı yazılı C testleri)
└── README.md           # Bu dosya
```

## 🚀 Kullanım

### Makefile ile

```bash
# Otomatik konfigürasyon (TEST_TYPE'a göre)
make isa                    # isa.json kullanır
make bench                  # bench.json kullanır
make arch                   # arch.json kullanır
make custom_test TEST=x     # custom.json kullanır

# Manuel konfigürasyon seçimi
make run TEST_CONFIG=isa
make run TEST_CONFIG=bench T=dhrystone

# Kustom test konfigürasyonu
make custom_config          # custom.json göster
make custom_list            # Mevcut testler listele

# Mevcut konfigürasyonu göster
make show-config

# Mevcut konfigürasyonları listele
make list-configs
```

### CLI ile

```bash
# Konfigürasyonları listele
./script/shell/parse_test_config.sh --list

# Konfigürasyonu görüntüle
./script/shell/parse_test_config.sh isa

# Make değişkenleri olarak çıktı
./script/shell/parse_test_config.sh isa --make

# Tek bir değer al
./script/shell/parse_test_config.sh coremark --get simulation.max_cycles

# SV defines string'i al
./script/shell/parse_test_config.sh bench --defines
```

## 📝 Konfigürasyon Yapısı

Her JSON dosyası aşağıdaki bölümleri içerebilir:

### `simulation` - Simülasyon Ayarları
```json
{
  "simulation": {
    "max_cycles": 10000,      // Maksimum simülasyon döngüsü
    "timeout_seconds": 60,    // Zaman aşımı (saniye)
    "parallel_jobs": "auto"   // Paralel test sayısı
  }
}
```

### `comparison` - RTL/Spike Karşılaştırma
```json
{
  "comparison": {
    "enabled": true,           // Karşılaştırmayı etkinleştir
    "use_pass_fail_addr": true,// Pass/fail adres kullan
    "spike_enabled": true      // Spike golden model
  }
}
```

### `defines` - SystemVerilog Define'lar
```json
{
  "defines": {
    "FAST_SIM": false,         // Hızlı simülasyon modu
    "KONATA_TRACE": true,      // Pipeline trace
    "BP_LOGGER_EN": false,     // Branch predictor log
    "CERES_UART_TX_MONITOR": false,
    "NO_COMMIT_TRACE": false,
    "NO_PIPELINE_LOG": false,
    "NO_RAM_LOG": false,
    "NO_UART_LOG": false
  }
}
```

### `trace` - Dalga Formu Ayarları
```json
{
  "trace": {
    "enabled": true,   // Trace etkin
    "format": "fst",   // fst veya vcd
    "depth": 99        // Sinyal derinliği
  }
}
```

### `logging` - Runtime Log Ayarları
```json
{
  "logging": {
    "commit_trace": true,
    "pipeline_log": true,
    "ram_log": true,
    "uart_log": true,
    "bp_log": false,
    "verbose": false
  }
}
```

### `build` - Derleme Ayarları
```json
{
  "build": {
    "mode": "debug",      // debug, release, profile
    "opt_level": "-O0",   // -O0, -O1, -O2, -O3
    "rebuild": false      // Her testte yeniden derle
  }
}
```

## 🔗 Miras (Inheritance)

Konfigürasyonlar `extends` alanı ile başka bir konfigürasyondan miras alabilir:

```json
{
  "extends": "default",
  "simulation": {
    "max_cycles": 100000
  }
}
```

Bu örnekte, `default.json`'daki tüm ayarlar alınır ve sadece `max_cycles` üzerine yazılır.

## ⚙️ Yeni Konfigürasyon Ekleme

1. Yeni bir JSON dosyası oluşturun:
```json
{
  "$schema": "./tests.schema.json",
  "_description": "My custom test configuration",
  "extends": "default",
  
  "simulation": {
    "max_cycles": 50000
  },
  
  "defines": {
    "MY_CUSTOM_DEFINE": true
  }
}
```

2. Makefile'da kullanın:
```bash
make run TEST_CONFIG=my_custom
```

## 🎯 Öncelik Sırası

1. **Komut satırı**: `make run MAX_CYCLES=5000` (en yüksek öncelik)
2. **JSON konfigürasyon**: `script/config/tests/*.json`
3. **Varsayılan değerler**: Makefile'larda tanımlı

## 📊 Konfigürasyon Karşılaştırması

| Özellik | ISA | Arch | Imperas | Bench | CoreMark |
|---------|-----|------|---------|-------|----------|
| max_cycles | 10K | 100K | 2M | 1M | 50M |
| trace | ✅ | ✅ | ❌ | ❌ | ❌ |
| FAST_SIM | ❌ | ❌ | ❌ | ✅ | ✅ |
| BP_LOG | ❌ | ❌ | ❌ | ✅ | ✅ |
| spike | ✅ | ✅ | ✅ | ❌ | ❌ |

## 🔧 Gereksinimler

- **jq**: JSON işleme için gerekli
  ```bash
  sudo apt install jq
  ```

jq yoksa sistem yine çalışır ama JSON konfigürasyonları yüklenmez, varsayılan değerler kullanılır.
