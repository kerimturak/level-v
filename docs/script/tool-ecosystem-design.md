# Tool Ecosystem Design Guide

Bu döküman, CERES projesi için geliştirilen tool ekosisteminin tasarım prensiplerini açıklar. Makefile, Python ve JSON konfigürasyonunun nasıl birlikte çalışması gerektiğini tanımlar.

---

## 🎯 Temel Prensipler

### 1. Separation of Concerns (Endişelerin Ayrılması)

```
┌─────────────────────────────────────────────────────────────────┐
│                         KULLANICI                               │
│                    make simulate T=test                         │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                        MAKEFILE                                 │
│  • Basit interface (make target)                                │
│  • Path ve değişken yönetimi                                    │
│  • Dependency management                                        │
│  • Kısa, okunabilir komutlar                                    │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                         PYTHON                                  │
│  • Karmaşık logic                                               │
│  • Validasyon ve hata yönetimi                                  │
│  • JSON parsing ve merging                                      │
│  • Renkli/formatlanmış çıktı                                    │
│  • Platform bağımsız işlemler                                   │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                          JSON                                   │
│  • Tüm konfigürasyon değerleri                                  │
│  • Profil tanımları                                             │
│  • Versiyon kontrolüne uygun                                    │
│  • İnsan tarafından okunabilir                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## 📁 Dosya Organizasyonu

```
script/
├── makefiles/           # Makefile modülleri
│   ├── config/          # Ortak konfigürasyon
│   │   ├── config.mk    # Ana ayarlar
│   │   ├── paths.mk     # Path tanımları
│   │   └── sources.mk   # Kaynak dosya listeleri
│   ├── sim/             # Simülatör hedefleri
│   │   ├── verilator.mk
│   │   └── modelsim.mk
│   └── tools/           # Yardımcı hedefler
│
├── python/              # Python scriptleri
│   └── makefile/        # Makefile'dan çağrılan scriptler
│       ├── modelsim_runner.py   # Simülasyon çalıştırıcı
│       └── modelsim_config.py   # Konfigürasyon yöneticisi
│
└── config/              # JSON konfigürasyonları
    ├── modelsim.json    # ModelSim ayarları
    ├── verilator.json   # Verilator ayarları
    └── tests.json       # Test tanımları
```

---

## 🔧 Katman Sorumlulukları

### Makefile Katmanı

**Yapması Gerekenler:**
- Basit target tanımları (`make simulate`, `make lint`)
- Path değişkenleri tanımlama ve export etme
- Dependency chain yönetimi
- Python script'i çağırma

**Yapmaması Gerekenler:**
- Karmaşık shell script blokları
- JSON parsing
- Conditional logic (basit olanlar hariç)
- Hata mesajı formatlama

```makefile
# ✅ DOĞRU: Basit ve temiz
simulate: compile
	$(PYTHON) $(MODELSIM_RUNNER) \
		--test $(TEST_NAME) \
		--config $(CONFIG_FILE) \
		--log-dir $(LOG_DIR)

# ❌ YANLIŞ: Karmaşık shell bloğu
simulate: compile
	@if [ -f $(MEM_FILE) ]; then \
		echo "Found"; \
		for dir in $(DIRS); do \
			if [ -d $$dir ]; then \
				# 50 satır daha shell kodu...
			fi; \
		done; \
	fi
```

### Python Katmanı

**Yapması Gerekenler:**
- JSON konfigürasyon okuma ve merge etme
- Validasyon ve schema kontrolü
- CLI argument parsing
- Renkli ve formatlanmış çıktı
- Dosya arama ve path işlemleri
- Subprocess yönetimi
- Hata yakalama ve raporlama

**Yapmaması Gerekenler:**
- Hardcoded path veya değerler
- Konfigürasyon varsayılanlarını kod içinde tutma

```python
# ✅ DOĞRU: Config'den al
sim_time = config.simulation.sim_time

# ❌ YANLIŞ: Hardcoded
sim_time = "100us"
```

### JSON Katmanı

**İçermesi Gerekenler:**
- Tüm varsayılan değerler
- Profil tanımları (debug, fast, coverage, vb.)
- Tool-specific ayarlar
- Açıklayıcı yorumlar (comment field olarak)

**İçermemesi Gerekenler:**
- Path'ler (bunlar Makefile'dan gelir)
- Çalışma zamanı değerleri

```json
{
  "_comment": "ModelSim/Questa Simulation Configuration",
  
  "simulation": {
    "sim_time": "100us",
    "time_resolution": "ns"
  },
  
  "profiles": {
    "fast": {
      "simulation": { "sim_time": "10us" },
      "lint": { "enabled": false }
    },
    "debug": {
      "debug": { "fsmdebug": true }
    }
  }
}
```

---

## 🎨 Renkli Console Çıktısı

### Renk Standardı

```python
class Color:
    # Durum renkleri
    RED = "\033[0;31m"      # Hatalar
    GREEN = "\033[0;32m"    # Başarı
    YELLOW = "\033[1;33m"   # Uyarılar
    
    # Bilgi renkleri  
    CYAN = "\033[0;36m"     # Bilgi mesajları
    BLUE = "\033[0;34m"     # Başlıklar
    WHITE = "\033[1;37m"    # Vurgulanan metin
    
    # Stiller
    DIM = "\033[2m"         # Soluk (secondary info)
    BOLD = "\033[1m"        # Kalın
    RESET = "\033[0m"       # Reset
```

### Çıktı Formatları

```
═══════════════════════════════════════════════════════════
  CERES RISC-V Simulation                          [HEADER]
═══════════════════════════════════════════════════════════

▶ Section Başlığı                                  [SECTION]
  Key:          Value                              [KEY-VAL]
  Başka Key:    Başka Value

[INFO] Bilgi mesajı                                [INFO]
[WARN] Uyarı mesajı                                [WARN]
[ERROR] Hata mesajı                                [ERROR]

════════════════════════════════════════════════════════════
  ✓ Başarılı                                       [SUCCESS]
════════════════════════════════════════════════════════════

════════════════════════════════════════════════════════════
  ✗ Başarısız                                      [FAILURE]
════════════════════════════════════════════════════════════
```

### Helper Fonksiyonlar

```python
def header(title: str, char: str = "═") -> None:
    """Ana başlık banner'ı"""
    width = 60
    print(f"\n{Color.CYAN}{char * width}{Color.RESET}")
    print(f"{Color.CYAN}  {title}{Color.RESET}")
    print(f"{Color.CYAN}{char * width}{Color.RESET}")

def subheader(title: str) -> None:
    """Alt başlık"""
    print(f"\n{Color.BLUE}▶ {title}{Color.RESET}")

def keyval(key: str, value: str, indent: int = 2) -> None:
    """Key-value çifti"""
    spaces = " " * indent
    print(f"{spaces}{Color.DIM}{key}:{Color.RESET} {value}")

def info(msg: str) -> None:
    print(f"{Color.CYAN}[INFO]{Color.RESET} {msg}")

def warn(msg: str) -> None:
    print(f"{Color.YELLOW}[WARN]{Color.RESET} {msg}", file=sys.stderr)

def error(msg: str) -> None:
    print(f"{Color.RED}[ERROR]{Color.RESET} {msg}", file=sys.stderr)

def success(msg: str) -> None:
    print(f"{Color.GREEN}[OK]{Color.RESET} {msg}")
```

### Renk Desteği Kontrolü

```python
import sys
import os

def supports_color() -> bool:
    """Terminal renk desteğini kontrol et"""
    # Pipe veya dosyaya yönlendirme varsa renk yok
    if not sys.stdout.isatty():
        return False
    
    # NO_COLOR environment variable (standard)
    if os.environ.get("NO_COLOR"):
        return False
    
    # TERM kontrolü
    term = os.environ.get("TERM", "")
    if term == "dumb":
        return False
    
    return True

# Script başlangıcında
if not supports_color():
    Color.disable()
```

---

## ⚙️ JSON Konfigürasyon Sistemi

### Schema Tanımlama

Her alan için tip, varsayılan değer ve geçerli seçenekler tanımlanmalı:

```python
CONFIG_SCHEMA = {
    "simulation": {
        "sim_time": {
            "type": "str",
            "default": "100us",
            "pattern": r"^\d+[pnum]?s$",
            "description": "Simülasyon süresi"
        },
        "time_resolution": {
            "type": "str",
            "default": "ns",
            "choices": ["ps", "ns", "us", "ms"],
            "description": "Zaman çözünürlüğü"
        }
    }
}
```

### Bilinmeyen Parametreler İçin Uyarı

```python
def validate_keys(data: dict, schema: dict, path: str = "") -> List[str]:
    """Bilinmeyen key'ler için uyarı üret"""
    warnings = []
    
    for key in data:
        full_path = f"{path}.{key}" if path else key
        
        if key not in schema:
            warnings.append(f"Bilinmeyen parametre: '{full_path}'")
        elif isinstance(data[key], dict) and isinstance(schema.get(key), dict):
            warnings.extend(validate_keys(data[key], schema[key], full_path))
    
    return warnings
```

### Profil Merge Sistemi

```python
def merge_profile(base: dict, profile: dict) -> dict:
    """Profili base config üzerine merge et"""
    result = copy.deepcopy(base)
    
    for key, value in profile.items():
        if isinstance(value, dict) and key in result:
            result[key] = merge_profile(result[key], value)
        else:
            result[key] = value
    
    return result
```

### CLI Override Tracking

```python
@dataclass
class ConfigValue:
    value: Any
    source: str  # "default", "json", "profile", "cli"
    
# Kullanım
if cli_args.sim_time:
    config.sim_time = ConfigValue(
        value=cli_args.sim_time,
        source="cli"
    )
```

---

## 📋 Makefile → Python Entegrasyonu

### Argüman Geçirme Standardı

```makefile
# Path'ler mutlak olmalı
RUNNER_ARGS := \
    --test $(TEST_NAME) \
    --work-dir $(abspath $(WORK_DIR)) \
    --log-dir $(abspath $(LOG_DIR)) \
    --config $(abspath $(CONFIG_FILE))

# Opsiyonel argümanlar
ifdef PROFILE
    RUNNER_ARGS += --profile $(PROFILE)
endif

ifdef SIM_TIME
    RUNNER_ARGS += --sim-time $(SIM_TIME)
endif

simulate:
    $(PYTHON) $(RUNNER) $(RUNNER_ARGS)
```

### Python Argparse Şablonu

```python
def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Tool Description",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    # Zorunlu argümanlar
    required = parser.add_argument_group("required arguments")
    required.add_argument("--test", required=True, help="Test adı")
    
    # Opsiyonel argümanlar
    parser.add_argument("--config", type=Path, help="JSON config dosyası")
    parser.add_argument("--profile", help="Config profili")
    parser.add_argument("--no-color", action="store_true", help="Renkleri devre dışı bırak")
    
    return parser.parse_args()
```

---

## 🧪 Test ve Validasyon

### Config Validation Target

```makefile
validate_config:
    $(PYTHON) $(CONFIG_MODULE) --validate --config $(CONFIG_FILE)

show_config:
    $(PYTHON) $(CONFIG_MODULE) --show --config $(CONFIG_FILE)
```

### Dry-Run Modu

```python
parser.add_argument(
    "--dry-run", "-n",
    action="store_true",
    help="Komutu çalıştırmadan göster"
)

# Kullanım
if args.dry_run:
    print(f"Would run: {' '.join(cmd)}")
    return 0
```

---

## 📊 Çıktı ve Loglama

### Summary JSON

Her çalışma sonunda summary oluştur:

```python
summary = {
    "test": config.test_name,
    "exit_code": exit_code,
    "elapsed_seconds": elapsed,
    "timestamp": datetime.now().isoformat(),
    "config": {
        "source": "json",
        "profile": config.profile_name,
        "cli_overrides": ["sim_time=100ns (JSON: 100us)"]
    },
    "settings": {
        "sim_time": config.sim_time,
        "voptargs": config.voptargs
    }
}

with open(log_dir / "summary.json", "w") as f:
    json.dump(summary, f, indent=2)
```

### Çıktı Yönlendirme

```python
# Hem console hem dosyaya yaz
with open(log_file, "w") as f:
    process = subprocess.Popen(cmd, stdout=PIPE, stderr=STDOUT, text=True)
    
    for line in process.stdout:
        print(line, end="")  # Console
        f.write(line)        # Dosya
```

---

## ✅ Kontrol Listesi

Yeni bir tool eklerken kontrol et:

### Makefile
- [ ] Target basit ve okunabilir mi?
- [ ] Path'ler `$(abspath ...)` ile mutlak mı?
- [ ] Dependency'ler doğru tanımlanmış mı?
- [ ] Help section güncellendi mi?

### Python
- [ ] JSON config desteği var mı?
- [ ] Bilinmeyen parametreler için uyarı var mı?
- [ ] Renkli çıktı desteği var mı?
- [ ] `--no-color` seçeneği var mı?
- [ ] Hata durumları handle ediliyor mu?
- [ ] Summary JSON oluşturuluyor mu?
- [ ] Dry-run modu var mı?

### JSON
- [ ] Tüm varsayılanlar tanımlı mı?
- [ ] Profiller mantıklı mı?
- [ ] Yorum (\_comment) alanları var mı?
- [ ] Schema dokümantasyonu var mı?

### Genel
- [ ] `make help` güncellendi mi?
- [ ] Dokümantasyon yazıldı mı?
- [ ] Örnek kullanım eklendi mi?

---

## 📖 Örnek: Yeni Tool Ekleme

### 1. JSON Config Oluştur

```json
// script/config/newtool.json
{
  "_comment": "New Tool Configuration",
  "version": "1.0",
  
  "defaults": {
    "timeout": 300,
    "verbose": false
  },
  
  "profiles": {
    "quick": { "timeout": 60 },
    "debug": { "verbose": true }
  }
}
```

### 2. Python Runner Yaz

```python
#!/usr/bin/env python3
"""New Tool Runner"""

from pathlib import Path
import argparse
import json
import subprocess

# Color ve helper fonksiyonları import et veya tanımla...

def main():
    args = parse_args()
    
    if not supports_color() or args.no_color:
        Color.disable()
    
    config = load_config(args.config, args.profile)
    
    header("New Tool")
    # ... işlemler
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
```

### 3. Makefile Target Ekle

```makefile
# script/makefiles/tools/newtool.mk

NEWTOOL_RUNNER := $(SCRIPT_DIR)/python/makefile/newtool_runner.py
NEWTOOL_CONFIG := $(SCRIPT_DIR)/config/newtool.json

newtool:
    $(PYTHON) $(NEWTOOL_RUNNER) \
        --config $(NEWTOOL_CONFIG) \
        $(if $(PROFILE),--profile $(PROFILE))

.PHONY: newtool
```

### 4. Ana Makefile'a Dahil Et

```makefile
include $(MAKEFILE_DIR)/tools/newtool.mk
```

---

## 🔍 Debug Logging

Her Python runner, detaylı debug log oluşturabilir. Bu loglar hata ayıklamayı kolaylaştırır.

### Debug Logger Kullanımı

```python
from debug_logger import create_logger, DebugLogger

# Logger oluştur
logger = create_logger(
    tool_name="verilator",      # veya "modelsim"
    log_dir=config.log_dir,
    debug_enabled=True          # veya CERES_DEBUG=1
)

# Bölüm başlat
logger.section("Configuration")

# Parametre logla (kaynak bilgisiyle)
logger.param("test_name", "rv32ui-p-add", source="cli")
logger.param("max_cycles", 100000, source="json")
logger.param("trace_enabled", True, source="default")

# Komut logla
logger.command(["vsim", "-c", ...], "ModelSim simulation")

# Dosya kontrolü
logger.file_check(Path("/path/to/file.mem"), "Memory file")

# Sonuç kaydet
logger.result(success=True, exit_code=0, message="Completed")
logger.save()
```

### Debug Modu Aktivasyonu

```bash
# Ortam değişkeni ile
CERES_DEBUG=1 make run_verilator TEST_NAME=rv32ui-p-add

# CLI flag ile
python verilator_runner.py --test rv32ui-p-add --debug

# Console'a da yazdırmak için
CERES_DEBUG=1 CERES_DEBUG_ECHO=1 make simulate TEST_NAME=test
```

### Debug Log Formatları

Her çalışmada iki format oluşturulur:

**1. Text Log (okunabilir)**
```
results/logs/verilator/test/debug_verilator_20251206_180823.log
results/logs/verilator/test/debug_verilator_latest.log  # Son çalışma
```

**2. JSON Log (parselanabilir)**
```
results/logs/verilator/test/debug_verilator_20251206_180823.json
results/logs/verilator/test/debug_verilator_latest.json
```

### Debug Log İçeriği

```
================================================================================
  CERES RISC-V — VERILATOR Debug Log
================================================================================
  Started: 2025-12-06 18:08:23
  CWD:     /home/kerim/level-v
  Python:  3.10.12
================================================================================

┌──────────────────────────────────────────────────────────────────────────────┐
│ CLI Arguments                                                                │
└──────────────────────────────────────────────────────────────────────────────┘
  [CLI ] test                      = rv32uc-p-rvc
  [CLI ] max_cycles                = 10000
  [CLI ] profile                   = None

┌──────────────────────────────────────────────────────────────────────────────┐
│ Run Configuration                                                            │
└──────────────────────────────────────────────────────────────────────────────┘
  [MERG] test_name                 = rv32uc-p-rvc
  [MERG] max_cycles                = 10000
  [MERG] cli_overrides             = ["max_cycles=10000 (JSON: 100000)"]

┌──────────────────────────────────────────────────────────────────────────────┐
│ Command                                                                      │
└──────────────────────────────────────────────────────────────────────────────┘
  ▶ Command: Verilator simulation
    $ /path/to/Vceres_wrapper 10000 +INIT_FILE=test.mem ...

┌──────────────────────────────────────────────────────────────────────────────┐
│ Results                                                                      │
└──────────────────────────────────────────────────────────────────────────────┘
  [EXEC] exit_code                 = 0
  [EXEC] elapsed_seconds           = 0.21
  ✅ Simulation passed: rv32uc-p-rvc

================================================================================
  ✅ SUCCESS - Simulation completed successfully
================================================================================
```

### Parametre Kaynakları

Debug log'da her parametrenin kaynağı gösterilir:

| Tag | Açıklama |
|-----|----------|
| `[CLI ]` | Komut satırından geldi |
| `[JSON]` | JSON config'den geldi |
| `[DEF ]` | Varsayılan değer |
| `[MERG]` | Merge edilmiş son değer |
| `[FOUN]` | Otomatik bulunan dosya |
| `[EXEC]` | Çalışma zamanında belirlendi |
| `[OVR ]` | Override edildi |

---

## 🔗 İlgili Dosyalar

- `script/python/makefile/debug_logger.py` - Debug logger modülü
- `script/python/makefile/modelsim_runner.py` - ModelSim runner (logger entegreli)
- `script/python/makefile/verilator_runner.py` - Verilator runner (logger entegreli)
- `script/python/makefile/modelsim_config.py` - Config yönetimi örneği
- `script/config/modelsim.json` - JSON config örneği
- `script/makefiles/sim/modelsim.mk` - Makefile entegrasyon örneği
