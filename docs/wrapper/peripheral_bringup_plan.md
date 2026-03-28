# Level-V — Çevre birimi (peripheral) sentez / FPGA bring-up planı

Bu plan, `rtl/wrapper/level_wrapper.sv` ve `sim/test/custom/*.c` ile uyumlu, **tek tek** doğrulama sırasını tanımlar.

## Kritik RTL durumu (önce oku)

| Yol | Çevre birimi | Durum |
|-----|----------------|--------|
| Wishbone PBUS (`pbus_addr`, `pbus_valid && sel_*`) | UART0 @ `0x2000_0xxx`, SPI0 @ `0x2001_0xxx`, I2C0 @ `0x2002_0xxx`, UART1 @ `0x2003_0xxx` | **Decode var** — `SPI_EN` / `I2C_EN` / `NUM_UART` ile açılır |
| `cpu_mem_req` + `sel_gpio` … | GPIO, GPTimer, PLIC, WDT, DMA, PWM, VGA | **`sel_gpio`, `sel_timer`, … şu an sabit `0`** — yazılım `0x20004xxx` vb. yazsa da IP seçilmiyor |
| Wishbone ayrı slave | CLINT @ `0x3000_0000` | **Bağlı** — `mtime` / `msip` vb. |

**Sonuç:** Sentezde yalnızca `*_EN` bayraklarını açmak, GPIO / Timer / PWM / PLIC / WDT / DMA / VGA testlerini **çalıştırmaz**; önce PBUS adres çözümlemesi ve bu IP’lerin **UART/SPI gibi `pbus_*` sinyallerine** bağlanması gerekir (bkz. `level_wrapper.sv` içindeki `sel_*` atamaları ve `gpio` / `gptimer` instance `stb_i` bağları).

Önce **Faz 0**’ı kod tarafında bitir; sonra aşağıdaki sentez adımları anlamlı olur.

---

## Faz 0 — RTL (önbüs + seçim hatları)

1. `pbus_addr[19:16]` (veya proje standardına uygun üst bitler) ile şunları atay:
   - `0x4` → GPIO (`0x20004000` ile uyumlu)
   - `0x5` → PWM (`0x20005000`)
   - `0x6` → GPTimer (`0x20006000`)
   - `0x7` → PLIC (`0x20007000`)
   - `0x8` → WDT (`0x20008000`) — *yorumda yoksa ekle*
   - `0x9` → DMA (`0x20009064`)
   - `0xA` → VGA (`0x2000A000`)
2. Her IP için: `stb_i = pbus_valid && sel_*`, adres/veri/yazma **`pbus_*`** ile beslensin (UART ile aynı desen).
3. **`pbus_rdata` mux** zaten `sel_*` dallarına hazır; decode düzeltilince okuma birleşir.
4. **DMA:** `dma_rdata_i` / `dma_ack_i` / `dreq_i` şu an TODO — tam işlevsel transfer testi bu bağlanana kadar **ertelenir**.
5. **PLIC:** `PLIC_EN=1` yapıldığında core `external interrupt` ile hizalanmalı (yazılım: `clint_test` / `interrupt_test` ile birlikte planla).

---

## Faz 1 — Zaten PBUS’ta olanlar (RTL Faz 0 sonrası veya mevcut UART ile)

| Sıra | Peripheral | Yazılım | FPGA / bench hazırlığı | Başarı |
|------|------------|---------|-------------------------|--------|
| 1.1 | **UART0** (programlama + log) | `uart_hello_test`, `uart_simple_test` | Host **115200**; `CPU_CLK_HZ` = sentez saati | Okunabilir ASCII |
| 1.2 | **SPI0** | `spi_test` | **MOSI–MISO loopback** (pin veya breadboard) | Gönderilen bayt ≈ alınan |
| 1.3 | **I2C0** | `i2c_test` | Sim’de model var; FPGA’da EEPROM veya **I2C analizörü** | ACK / veri tutarlılığı |
| 1.4 | **UART1** (isteğe bağlı) | Ayrı küçük test | `NUM_UART=2`, ikinci TX/RX pin | İki kanal ayrı metin |

`level_wrapper` parametreleri: `SPI_EN=1`, `I2C_EN=1`, gerekirse `NUM_UART=2`.

---

## Faz 2 — Faz 0 decode + enable sonrası: MMIO blokları

| Sıra | Peripheral | Yazılım | Dikkat | Başarı |
|------|------------|---------|--------|--------|
| 2.1 | **GPTimer** | `timer_test` | IRQ’yu görmek için PLIC veya bayrak okuma | Counter / prescaler / bayrak |
| 2.2 | **GPIO** | `gpio_test` | Bazı pinleri çıkış, jumper ile girişe loopback veya LED | OUT/IN tutarlı |
| 2.3 | **PWM** | `pwm_test` | Osiloskop veya LED parlaklığı | Frekans/duty kabaca beklenen |
| 2.4 | **PLIC** | `plic_test` | Harici veya timer kaynaklı IRQ | Claim/complete, öncelik |
| 2.5 | **WDT** | `wdt_test` | **RST çıkışı** — kartı resetleyebilir; önce sim | Sayım, unlock, *istenirse* EW IRQ |
| 2.6 | **VGA** | `vga_test` | Pixel clock / monitör veya sadece MMIO smoke | Kontrol yazıp okuma |

Parametreler: `TIMER_EN`, `GPIO_EN`, `PWM_EN`, `PLIC_EN`, `WDT_EN`, `VGA_EN` sırayla `1`.

---

## Faz 3 — DMA (bus tamamlanınca)

| Peripheral | Yazılım | Önkoşul | Başarı |
|------------|---------|---------|--------|
| **DMA** | `dma_test` | Master port RAM’e bağlı, `dma_ack` / `rdata` gerçek | M2M veya çevre biriminden belleğe kopya + IRQ |

---

## Faz 4 — Birleşik / stres

- `cache_test`, `interrupt_test`, `exception_test`, `csr_test` — çekirdek + bellek + (varsa) IRQ
- Üretim öncesi: tüm açık IP’ler için tek bitstream + regresyon `.mem` listesi

---

## Sentez / constraint checklist

- Her yeni pin için XDC: `PACKAGE_PIN`, `IOSTANDARD`, gerekirse `PULLUP` (I2C)
- SPI/I2C hızı: yazılım `clk_div` / `sck_div` değerlerini **gerçek CPU_CLK** ile gözden geçir
- `CPU_CLK` ve C tarafı `CPU_CLK_HZ` / `cpu_clock.h` aynı olmalı

---

## Özet akış

```mermaid
flowchart LR
  A[Faz 0 RTL PBUS decode] --> B[UART + SPI + I2C]
  B --> C[Timer GPIO PWM]
  C --> D[PLIC WDT VGA]
  D --> E[DMA bus]
```

İlk somut adım: **Faz 0** olmadan GPIO/Timer testlerini FPGA’da beklemeyin; sonuç alınamaz.
