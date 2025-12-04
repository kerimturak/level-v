# Single-Port Block RAM Modülü - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Write-First Modu](#write-first-modu)
4. [FPGA Sentezi](#fpga-sentezi)
5. [Kullanım Örnekleri](#kullanım-örnekleri)

---

## Genel Bakış

### Amaç

`sp_bram` modülü, **Write-First** modunda çalışan tek portlu Block RAM şablonudur. Xilinx FPGA'lerde verimli BRAM inferencing için optimize edilmiştir.

### Dosya Konumu

```
rtl/ram/sp_bram.sv
```

### Temel Özellikler

| Özellik | Değer |
|---------|-------|
| **Port Sayısı** | 1 (Single-port) |
| **Write Modu** | Write-First |
| **Parametrik** | Genişlik ve derinlik |
| **FPGA Uyumlu** | Xilinx BRAM inference |

---

## Modül Arayüzü

### Port Tanımları

```systemverilog
module sp_bram #(
    parameter DATA_WIDTH = 32,   // Veri genişliği
    parameter NUM_SETS   = 1024  // Set sayısı (derinlik)
) (
    input  logic                        clk,      // Clock sinyali
    input  logic                        chip_en,  // Chip enable
    input  logic [$clog2(NUM_SETS)-1:0] addr,     // Adres
    input  logic                        wr_en,    // Write enable
    input  logic [      DATA_WIDTH-1:0] wr_data,  // Yazma verisi
    output logic [      DATA_WIDTH-1:0] rd_data   // Okuma verisi
);
```

### Parametre Tablosu

| Parametre | Varsayılan | Açıklama |
|-----------|------------|----------|
| `DATA_WIDTH` | 32 | Veri bus genişliği (bit) |
| `NUM_SETS` | 1024 | Bellek derinliği (satır) |

---

## Write-First Modu

### Davranış

Write-First modunda, yazma işlemi sırasında yeni veri hem belleğe yazılır hem de okuma portuna yansıtılır:

```systemverilog
always @(posedge clk) begin
    if (chip_en) begin
        if (wr_en) begin
            bram[addr] <= wr_data;   // Belleğe yaz
            rd_data    <= wr_data;   // Yeni veriyi çıkışa ver
        end else begin
            rd_data <= bram[addr];   // Normal okuma
        end
    end
end
```

### Zamanlama Diyagramı

```
clk      ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

chip_en  ────/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\────

addr     ────┤ A1 ├────┤ A2 ├──────────────

wr_en    ────/‾‾‾‾\────────────────────────
              WRITE      READ

wr_data  ────┤ D1 ├────────────────────────

rd_data  ──────────┤ D1 ├────┤bram[A2]├────
                   (write-   (normal
                    first)    read)
```

### Write Modları Karşılaştırması

| Mod | Yazma Sırasında rd_data | Kullanım |
|-----|-------------------------|----------|
| **Write-First** | Yeni veri (wr_data) | Read-after-write aynı cycle |
| Read-First | Eski veri | Eski değer gerektiğinde |
| No-Change | Değişmez | Güç optimizasyonu |

---

## FPGA Sentezi

### Xilinx BRAM Inference

Bu şablon, Xilinx Vivado tarafından otomatik olarak BRAM olarak sentezlenir:

```
Inference Koşulları:
✓ Senkron okuma (registered output)
✓ Tek clock domain
✓ chip_en ile gated
✓ Write-first pattern
```

### Resource Kullanımı

| Konfigürasyon | BRAM18K | BRAM36K |
|---------------|---------|---------|
| 32x1024 | 1 | 0.5 |
| 32x2048 | 2 | 1 |
| 32x4096 | 4 | 2 |
| 128x1024 | 4 | 2 |

---

## Kullanım Örnekleri

### Cache Data Array

```systemverilog
sp_bram #(
    .DATA_WIDTH(128),    // Cache line width
    .NUM_SETS  (64)      // 64 sets
) u_cache_data (
    .clk    (clk_i),
    .chip_en(1'b1),
    .addr   (set_index),
    .wr_en  (cache_write),
    .wr_data(write_line),
    .rd_data(read_line)
);
```

### Register File

```systemverilog
sp_bram #(
    .DATA_WIDTH(32),
    .NUM_SETS  (32)
) u_regfile (
    .clk    (clk_i),
    .chip_en(1'b1),
    .addr   (reg_addr),
    .wr_en  (rf_we),
    .wr_data(rf_wdata),
    .rd_data(rf_rdata)
);
```

---

## Özet

`sp_bram` modülü:

1. **Write-First**: Yazma anında yeni veri çıkışta
2. **Parametrik**: Genişlik ve derinlik ayarlanabilir
3. **FPGA Optimized**: Xilinx BRAM inference
4. **Single-Port**: Basit arayüz

Cache ve register file gibi yapılar için temel bellek bloğu olarak kullanılır.
