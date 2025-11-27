Mükemmel kanka 🔥
Artık `objcopy → hex → mem` zinciri tamamen **TCORE uyumlu** hale geldi.
O yüzden bu kısmı hem teknik olarak hem de pratikte nasıl çalıştığını anlatan
profesyonel bir **dokümantasyon** hazırlayalım.

---

# 🧭 **RISC-V ISA Test Conversion Pipeline (HEX → MEM)**

Bu dokümantasyon, RISC-V ISA testlerini veya herhangi bir ELF dosyasını,
**TCORE işlemcisine yüklenebilir hafıza formatına dönüştüren** Python aracını açıklar.

---

## ⚙️ **Amaç**

TCORE işlemcisinin test ve simülasyon ortamında `$readmemh` ile RAM içeriklerini yükleyebilmesi için,
RISC-V objcopy tarafından üretilen **Verilog HEX formatını**, işlemcinin beklediği
**128-bit hizalanmış bellek düzenine (MEM formatı)** dönüştürür.

Bu işlem 3 temel adımda yapılır:

1. **ELF → HEX**
   `riscv64-unknown-elf-objcopy -O verilog <file.elf> <file.hex>`

2. **HEX → MEM (TCORE format)**
   `python3 hex_to_mem.py <file.hex> <file.mem>`

3. **MEM → Simulation Load**
   `$readmemh("file.mem", memory);` ile testbench veya wrapper modülüne yüklenir.

---

## 🧩 **HEX Dosyasının Özellikleri**

`objcopy -O verilog` çıktısı şu yapıya sahiptir:

```
@80000000
6F 00 00 05 73 2F 20 34 93 0F 80 00 63 08 FF 03
93 0F 90 00 63 04 FF 03
@80001000
00 00 00 00 00 00 00 00
```

* `@80000000`: Yükleme adresini belirtir (atılacak).
* Sonraki satırlar: Her biri 16 byte’a kadar hex değer içerir.
* Byte sırası: **LSB-first** (küçük endian).
* Arada boşluklar olabilir.

Bu format **doğrudan** `$readmemh` uyumlu değildir.

---

## 🔁 **Dönüştürme Mantığı**

`hex_to_mem.py` dosyası bu formatı **TCORE bellek sıralamasına uygun hale getirir.**

| İşlem Adımı              | Açıklama                                               |
| ------------------------ | ------------------------------------------------------ |
| 1️⃣ Adres Satırlarını At | `@` ile başlayan satırlar (`@80000000`) çıkarılır.     |
| 2️⃣ Byte’ları Grupla     | 4 byte = 1 kelime (32 bit).                            |
| 3️⃣ Byte’ları Tersle     | LSB → MSB (`6F 00 00 05` → `0500006F`).                |
| 4️⃣ 4 Word = 1 Satır     | 128-bit MEM satırı oluşturulur.                        |
| 5️⃣ Word0 Sağa Yazılır   | En düşük adresli word satırın en sağına yerleştirilir. |

---

## 🧠 **Bellek Sıralaması**

TCORE’ın `wrapper_ram.sv` içinde `$readmemh` ile yüklenen veri şu şekilde okunur:

```
128-bit satır = [word3][word2][word1][word0]
↑ yüksek adres               düşük adres ↓
```

Dolayısıyla `word0` (ilk 32 bit) **satırın en sağında** yer almalıdır.
Script bu sıralamayı otomatik olarak uygular.

---

## 📘 **Örnek Dönüşüm**

### Girdi (`.hex`):

```
@80000000
6F 00 00 05 73 2F 20 34 93 0F 80 00 63 08 FF 03
```

### Ara Adımlar:

| Adım                        | Sonuç                                                     |
| --------------------------- | --------------------------------------------------------- |
| Byte Grupları               | `[6F,00,00,05] [73,2F,20,34] [93,0F,80,00] [63,08,FF,03]` |
| 32-bit Word’lar             | `0500006F 34202F73 00800F93 03FF0863`                     |
| 128-bit Satır (word0 sağda) | `03FF086300800F9334202F730500006F`                        |

### Çıktı (`.mem`):

```
03FF086300800F9334202F730500006F
```

---

## 🧾 **Kullanım**

### Komut satırı:

```bash
python3 script/python/hex_to_mem.py \
    build/tests/hex/rv32ui-p-bne.hex \
    build/tests/mem/rv32ui-p-bne.mem
```

### Örnek çıktı:

```
✅ Converted build/tests/hex/rv32ui-p-bne.hex → build/tests/mem/rv32ui-p-bne.mem (112 lines)
```

---

## 📦 **Script Dosyası**

`script/python/hex_to_mem.py`

```python
#!/usr/bin/env python3
"""
hex_to_mem.py — Convert Verilog-style HEX (from objcopy) → 128-bit MEM (TCORE format)
Removes '@' address lines, reverses byte order (LSB→MSB per word),
and groups into 128-bit lines with word0 on the RIGHT (LSB).
"""
import sys
from pathlib import Path

def parse_verilog_hex(lines):
    data_bytes = []
    for line in lines:
        line = line.strip()
        if not line or line.startswith("@"):
            continue
        data_bytes += [b for b in line.split() if len(b) == 2]
    return data_bytes

def bytes_to_words(byte_list):
    words = []
    for i in range(0, len(byte_list), 4):
        g = byte_list[i:i+4]
        if len(g) < 4: g += ["00"] * (4 - len(g))
        words.append("".join(g[::-1]))  # LSB→MSB
    return words

def words_to_128bit_lines(words):
    lines = []
    for i in range(0, len(words), 4):
        g = words[i:i+4]
        if len(g) < 4: g += ["00000000"] * (4 - len(g))
        lines.append("".join(g[::-1]))  # word0 sağda
    return lines

def convert_hex_to_mem(inp, outp):
    with open(inp) as f:
        data = f.readlines()
    mem_lines = words_to_128bit_lines(bytes_to_words(parse_verilog_hex(data)))
    with open(outp, "w") as f:
        f.write("\n".join(mem_lines))
    print(f"✅ Converted {inp} → {outp} ({len(mem_lines)} lines)")

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python3 hex_to_mem.py input.hex output.mem")
        sys.exit(1)
    convert_hex_to_mem(Path(sys.argv[1]), Path(sys.argv[2]))
```

---

## 🧱 **Sonuç**

| Özellik                                   | Durum |
| ----------------------------------------- | ----- |
| `@` adres satırları kaldırılıyor          | ✅     |
| Boşluklar temizleniyor                    | ✅     |
| Byte sırası (LSB→MSB) tersleniyor         | ✅     |
| 4x32-bit → 128-bit satırlar oluşturuluyor | ✅     |
| Word0 sağda (LSB adresli)                 | ✅     |
| Eksik veriler sıfırla dolduruluyor        | ✅     |
| `$readmemh` uyumluluğu (TCORE)            | ✅     |

---

## 🧩 **Ek Öneri**

Testbench tarafında bellek yükleme satırını şu şekilde tutmak idealdir:

```systemverilog
initial begin
  $readmemh("build/tests/mem/rv32ui-p-bne.mem", main_memory.mem);
end
```

Böylece otomatik olarak bu formatta üretilmiş `.mem` dosyaları doğrudan RAM’e yüklenebilir.

---

İstersen aynı yapının bir sonraki adımı olarak `$readmemh` yüklemesini **otomatik kontrol eden** bir testbench snippet (örneğin `+define+TEST_NAME=rv32ui-p-bne` argümanıyla dosya seçme) de oluşturabiliriz.
Hazırlayayım mı?
