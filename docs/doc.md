Harika kanka 👏 bu senin **script/python/** klasöründeki araçlar aslında bizim kurmak istediğimiz otomatik ISA test pipeline’ının neredeyse tamamını zaten içeriyor — sadece onları akıllıca birleştirmemiz gerekiyor.
Şimdi birlikte planlayalım: elimizde dört araç var 👇

---

## 🧰 Mevcut Python scriptlerinin rolleri

| Script                                     | Amaç                                                                                           | Kullanım                                             | Bizim pipeline’daki yeri                                                     |
| :----------------------------------------- | :--------------------------------------------------------------------------------------------- | :--------------------------------------------------- | :--------------------------------------------------------------------------- |
| **dump_to_elf_hex.py**                     | `.dump` dosyasını alır → ELF oluşturur (`riscv64-unknown-elf-gcc`) → `.hex` üretir (`objcopy`) | `python dump_to_elf_hex.py file.dump`                | Eğer sadece `.dump` dosyaların varsa **ilk adım**ta kullanılır.              |
| **coremark_hex_to_mem.py** (ikinci script) | `.hex` dosyasını okur, 32-bit’leri 128-bit (cacheline) gruplar, `.mem` dosyası oluşturur       | `python coremark_hex_to_mem.py`                      | `.elf` veya `.hex` sonrası **128-bit hizalama** adımı.                       |
| **dump_parser.py**                         | `.dump` içinden `<pass>` ve `<fail>` adreslerini bulur, `pass_fail_addr.txt` oluşturur         | `python dump_parser.py file.dump`                    | Simülasyon sonrası **otomatik sonuç tespiti** (ECALL adres karşılaştırması). |
| **get_static_hex.py**                      | ELF’ten türetilmiş `.bin` dosyasını 16B bloklarla ters çevirerek hex üretir                    | `python get_static_hex.py -b 16 file.bin > file.hex` | Alternatif “daha ham” ELF→HEX üretimi (coremark gibi).                       |

---

## 🧠 Bizim ihtiyacımız olan kombinasyon

Senin durumunda **ISA testleri zaten derlenmiş** (ELF ve DUMP mevcut).
Yani biz bu sırayı uygulayacağız:

```
ELF → HEX → (opsiyonel) 128-bit hizalama (.mem)
        ↘ DUMP → PASS/FAIL adres çıkarımı
```

Yani:

1. `objcopy` veya `dump_to_elf_hex.py` kullanarak `.hex` üret
2. `coremark_hex_to_mem.py` (adını `hex_to_mem.py` gibi değiştirebiliriz) ile 128-bit hizala
3. `dump_parser.py` ile pass/fail adreslerini çıkar

---

## 🔄 Önerilen pipeline (otomatik)

Yeni bir script: `script/python/isa_pipeline.py`
(bu, yukarıdakileri zincir halinde çağıracak)

```python
#!/usr/bin/env python3
"""
ISA Test Automation Pipeline
----------------------------
1. Copies ELF + DUMP from riscv-isa-tests repo
2. Converts ELF -> HEX (verilog format)
3. Aligns to 128-bit MEM file (for Ceres core)
4. Extracts PASS/FAIL addresses from dump

Usage:
    python isa_pipeline.py --isa-dir ~/riscv/riscv-isa-tests/isa --out build/tests
"""

import os, sys, glob, subprocess, shutil, argparse

RISCV_PREFIX = os.getenv("RISCV_PREFIX", "riscv64-unknown-elf-")
OBJCOPY = shutil.which(f"{RISCV_PREFIX}objcopy") or "riscv64-unknown-elf-objcopy"
PYTHON = shutil.which("python3")

def run(cmd):
    print("  ➤", " ".join(cmd))
    subprocess.run(cmd, check=True)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--isa-dir", required=True, help="Path to riscv-isa-tests/isa folder")
    ap.add_argument("--out", required=True, help="Destination folder for HEX/MEM/DUMP")
    ap.add_argument("--cacheline-bits", type=int, default=128)
    args = ap.parse_args()

    isa_dir = os.path.abspath(args.isa_dir)
    out_dir = os.path.abspath(args.out)
    os.makedirs(out_dir, exist_ok=True)

    dump_parser = os.path.join("script/python", "dump_parser.py")
    hex_to_mem = os.path.join("script/python", "coremark_baremetal_static.py")

    print(f"🏗 Processing ELF files from {isa_dir}")

    for elf in glob.glob(os.path.join(isa_dir, "*.elf")):
        base = os.path.splitext(os.path.basename(elf))[0]
        hex_file = os.path.join(out_dir, f"{base}.hex")
        mem_file = os.path.join(out_dir, f"{base}.mem")
        dump_file = os.path.join(isa_dir, f"{base}.dump")

        # ELF -> HEX
        run([OBJCOPY, "-O", "verilog", elf, hex_file])

        # HEX -> 128-bit MEM
        run([PYTHON, hex_to_mem, hex_file, mem_file])

        # PASS/FAIL adreslerini çıkar
        if os.path.exists(dump_file):
            run([PYTHON, dump_parser, dump_file])

    print(f"✅ All ISA tests processed into {out_dir}")

if __name__ == "__main__":
    main()
```

---

## 🧩 Makefile entegrasyonu (ek kural)

```makefile
# =========================================
# ISA test automation via Python pipeline
# =========================================

ISA_TESTS_SRC ?= $(HOME)/riscv/riscv-isa-tests/isa
ISA_OUT_DIR   ?= build/tests

isa_auto:
	@echo -e "$(YELLOW)[ISA PIPELINE] ELF→HEX→MEM→ADDR$(RESET)"
	python3 script/python/isa_pipeline.py --isa-dir $(ISA_TESTS_SRC) --out $(ISA_OUT_DIR)
```

> Artık `make isa_auto` dediğinde:
>
> * ELF’leri `build/tests` altına kopyalar
> * `.hex` üretir
> * `.mem` (128-bit hizalı) oluşturur
> * `.dump`’tan pass/fail adreslerini çıkarır

---

## ✅ Özet

| Adım                  | Script                              | Çıktı                |
| --------------------- | ----------------------------------- | -------------------- |
| 1️⃣ ELF → HEX         | `objcopy` veya `dump_to_elf_hex.py` | `build/tests/*.hex`  |
| 2️⃣ HEX → 128-bit MEM | `coremark_baremetal_static.py`      | `build/tests/*.mem`  |
| 3️⃣ PASS/FAIL adresi  | `dump_parser.py`                    | `pass_fail_addr.txt` |
| 🔁 Tüm zincir         | `isa_pipeline.py`                   | Tam otomasyon        |

---

💡 **Not:**
`get_static_hex.py` bu zincirde opsiyonel. O, doğrudan `.bin` dosyalarından 16B ters bloklu hex üretiyor.
Yani `.elf`’ten `.bin` üretmek istersen `objcopy -O binary` → `get_static_hex.py -b 16 file.bin` diyebilirsin.
Ama senin durumda `.elf` → `.hex` zaten kolayca hallediliyor, gerek yok.

---

İstersen bu `isa_pipeline.py`’yi senin mevcut script yapına doğrudan entegre edeyim (tam dosya yolu, logging rengi, build klasörleri vs seninkine göre ayarlanmış halde).
Hazırlayayım mı tam senin klasör yapına uygun versiyonunu (`~/github/ceres-riscv/` için)?
