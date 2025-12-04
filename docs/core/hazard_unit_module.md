# Hazard Unit Modülü - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [Data Hazard Tipleri](#data-hazard-tipleri)
4. [Forwarding Mekanizması](#forwarding-mekanizması)
5. [Stall Mekanizması](#stall-mekanizması)
6. [Flush Mekanizması](#flush-mekanizması)
7. [Karar Matrisi](#karar-matrisi)
8. [Zamanlama Diyagramları](#zamanlama-diyagramları)
9. [Performans Analizi](#performans-analizi)
10. [Doğrulama ve Test](#doğrulama-ve-test)

---

## Genel Bakış

### Amaç

`hazard_unit` modülü, 5-aşamalı pipeline'da oluşabilecek **data hazard**'ları tespit eder ve çözer. Bu modül, işlemcinin doğru sonuçlar üretmesini sağlamak için **forwarding** (veri yönlendirme) ve **stall** (pipeline durdurma) mekanizmalarını kontrol eder.

### Temel Özellikler

| Özellik | Değer |
|---------|-------|
| **Hazard Tipleri** | RAW (Read After Write), Control |
| **Forwarding Yolları** | MEM→EX, WB→EX, WB→DE |
| **Stall Desteği** | Load-Use hazard |
| **Flush Desteği** | Branch misprediction |
| **Kombinasyonel Tasarım** | Tam kombinasyonel (register yok) |

### Hazard Unit Blok Diyagramı

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                               HAZARD UNIT                                        │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│   ┌───────────────────────────────────────────────────────────────────────┐     │
│   │                    REGISTER ADRESLERİ                                  │     │
│   │                                                                        │     │
│   │   Decode Stage     Execute Stage     Memory Stage    Writeback Stage  │     │
│   │   ┌─────────┐      ┌─────────┐       ┌─────────┐     ┌─────────┐      │     │
│   │   │r1_addr  │      │r1_addr  │       │rd_addr  │     │rd_addr  │      │     │
│   │   │r2_addr  │      │r2_addr  │       │rf_rw    │     │rf_rw    │      │     │
│   │   └────┬────┘      │rd_addr  │       └────┬────┘     └────┬────┘      │     │
│   │        │           └────┬────┘            │               │           │     │
│   └────────┼────────────────┼─────────────────┼───────────────┼───────────┘     │
│            │                │                 │               │                  │
│            ▼                ▼                 ▼               ▼                  │
│   ┌────────────────────────────────────────────────────────────────────────┐    │
│   │                        COMPARATOR MATRIX                                │    │
│   │                                                                         │    │
│   │   ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐        │    │
│   │   │  EX vs MEM      │  │  EX vs WB       │  │  DE vs WB       │        │    │
│   │   │  Forwarding     │  │  Forwarding     │  │  Forwarding     │        │    │
│   │   └────────┬────────┘  └────────┬────────┘  └────────┬────────┘        │    │
│   │            │                    │                    │                  │    │
│   └────────────┼────────────────────┼────────────────────┼──────────────────┘    │
│                │                    │                    │                       │
│                ▼                    ▼                    ▼                       │
│   ┌────────────────────────────────────────────────────────────────────────┐    │
│   │                         OUTPUT GENERATION                               │    │
│   │                                                                         │    │
│   │   fwd_a_ex[1:0]    fwd_b_ex[1:0]    fwd_a_de    fwd_b_de               │    │
│   │   stall_fe         stall_de         flush_de    flush_ex                │    │
│   │                                                                         │    │
│   └────────────────────────────────────────────────────────────────────────┘    │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## Modül Arayüzü

### Port Tanımları

```systemverilog
module hazard_unit (
    // Decode Stage Register Adresleri
    input  logic [4:0] r1_addr_de_i,    // Decode rs1 adresi
    input  logic [4:0] r2_addr_de_i,    // Decode rs2 adresi
    
    // Execute Stage Register Adresleri
    input  logic [4:0] r1_addr_ex_i,    // Execute rs1 adresi
    input  logic [4:0] r2_addr_ex_i,    // Execute rs2 adresi
    input  logic [4:0] rd_addr_ex_i,    // Execute rd adresi
    
    // Execute Stage Control
    input  logic       pc_sel_ex_i,     // Branch/Jump alındı mı
    input  logic       rslt_sel_ex_0,   // Load instruction mı (result_src[0])
    
    // Memory Stage
    input  logic [4:0] rd_addr_me_i,    // Memory rd adresi
    input  logic       rf_rw_me_i,      // Memory register write enable
    
    // Writeback Stage
    input  logic       rf_rw_wb_i,      // Writeback register write enable
    input  logic [4:0] rd_addr_wb_i,    // Writeback rd adresi
    
    // Stall Çıkışları
    output logic       stall_fe_o,      // Fetch stage stall
    output logic       stall_de_o,      // Decode stage stall
    
    // Flush Çıkışları
    output logic       flush_de_o,      // Decode stage flush
    output logic       flush_ex_o,      // Execute stage flush
    
    // Forwarding Çıkışları
    output logic [1:0] fwd_a_ex_o,      // Execute rs1 forwarding select
    output logic [1:0] fwd_b_ex_o,      // Execute rs2 forwarding select
    output logic       fwd_a_de_o,      // Decode rs1 forwarding
    output logic       fwd_b_de_o       // Decode rs2 forwarding
);
```

### Port Açıklamaları

#### Giriş Portları - Decode Stage

| Port | Genişlik | Açıklama |
|------|----------|----------|
| `r1_addr_de_i` | 5 bit | Decode aşamasındaki instruction'ın rs1 register adresi |
| `r2_addr_de_i` | 5 bit | Decode aşamasındaki instruction'ın rs2 register adresi |

#### Giriş Portları - Execute Stage

| Port | Genişlik | Açıklama |
|------|----------|----------|
| `r1_addr_ex_i` | 5 bit | Execute aşamasındaki instruction'ın rs1 register adresi |
| `r2_addr_ex_i` | 5 bit | Execute aşamasındaki instruction'ın rs2 register adresi |
| `rd_addr_ex_i` | 5 bit | Execute aşamasındaki instruction'ın hedef register (rd) adresi |
| `pc_sel_ex_i` | 1 bit | Branch/Jump alındı sinyali (1 = taken, 0 = not taken) |
| `rslt_sel_ex_0` | 1 bit | Result source bit 0 (1 = load instruction, memory'den oku) |

#### Giriş Portları - Memory Stage

| Port | Genişlik | Açıklama |
|------|----------|----------|
| `rd_addr_me_i` | 5 bit | Memory aşamasındaki instruction'ın rd adresi |
| `rf_rw_me_i` | 1 bit | Memory aşamasının register file yazma enable sinyali |

#### Giriş Portları - Writeback Stage

| Port | Genişlik | Açıklama |
|------|----------|----------|
| `rd_addr_wb_i` | 5 bit | Writeback aşamasındaki instruction'ın rd adresi |
| `rf_rw_wb_i` | 1 bit | Writeback aşamasının register file yazma enable sinyali |

#### Çıkış Portları - Stall

| Port | Genişlik | Açıklama |
|------|----------|----------|
| `stall_fe_o` | 1 bit | Fetch aşamasını durdur |
| `stall_de_o` | 1 bit | Decode aşamasını durdur |

#### Çıkış Portları - Flush

| Port | Genişlik | Açıklama |
|------|----------|----------|
| `flush_de_o` | 1 bit | Decode pipeline register'ını temizle |
| `flush_ex_o` | 1 bit | Execute pipeline register'ını temizle |

#### Çıkış Portları - Forwarding

| Port | Genişlik | Açıklama |
|------|----------|----------|
| `fwd_a_ex_o` | 2 bit | Execute rs1 için forwarding seçimi |
| `fwd_b_ex_o` | 2 bit | Execute rs2 için forwarding seçimi |
| `fwd_a_de_o` | 1 bit | Decode rs1 için WB'den forwarding |
| `fwd_b_de_o` | 1 bit | Decode rs2 için WB'den forwarding |

---

## Data Hazard Tipleri

### RAW (Read After Write) Hazard

RAW hazard, bir instruction'ın henüz yazılmamış bir register'ı okumaya çalışması durumunda oluşur.

```
Cycle:     1      2      3      4      5
         ┌──────┬──────┬──────┬──────┬──────┐
ADD x1   │  IF  │  DE  │  EX  │  MEM │  WB  │  ← x1'e yazar
         └──────┴──────┴──────┴──────┴──────┘
               ┌──────┬──────┬──────┬──────┬──────┐
SUB x2,x1│     │  IF  │  DE  │  EX  │  MEM │  WB  │  ← x1'i okur
               └──────┴──────┴──────┴──────┴──────┘
                        ↑
                        │ RAW Hazard: x1 henüz yazılmadı!
```

### RAW Hazard Kategorileri

| Kategori | Mesafe | Kaynak → Hedef | Çözüm |
|----------|--------|----------------|-------|
| **EX-EX** | 1 cycle | MEM → EX | Forwarding |
| **MEM-EX** | 2 cycle | WB → EX | Forwarding |
| **WB-DE** | 3 cycle | WB → DE | Forwarding |
| **Load-Use** | 1 cycle | MEM (load) → EX | Stall + Forward |

### Load-Use Hazard

Load instruction'ın sonucu sadece MEM aşamasında hazır olur, bu yüzden hemen sonraki instruction tarafından kullanılamaz.

```
Cycle:     1      2      3      4      5      6
         ┌──────┬──────┬──────┬──────┬──────┐
LW x1    │  IF  │  DE  │  EX  │  MEM │  WB  │  ← x1 MEM'de hazır
         └──────┴──────┴──────┴──────┴──────┘
               ┌──────┬──────┬──────┬──────┬──────┐
ADD x2,x1│     │  IF  │  DE  │ stall│  EX  │  MEM │  WB
               └──────┴──────┴──────┴──────┴──────┘
                              ↑
                              │ 1 cycle stall (bubble)
                              │ Sonra MEM→EX forward
```

### Control Hazard

Branch veya jump instruction'ın hedef adresi execute aşamasında hesaplanır. Yanlış tahmin durumunda pipeline'daki spekülatif instruction'lar flush edilmelidir.

```
Cycle:     1      2      3      4      5
         ┌──────┬──────┬──────┬──────┬──────┐
BEQ x1,x2│  IF  │  DE  │  EX  │  MEM │  WB  │  ← EX'de karar
         └──────┴──────┴──────┴──────┴──────┘
               ┌──────┬──────┐
Wrong I1 │     │  IF  │  DE  │ flush │        ← Yanlış yoldaki instr
               └──────┴──────┘
                     ┌──────┐
Wrong I2       │     │  IF  │ flush │          ← Yanlış yoldaki instr
                     └──────┘
                              ┌──────┬──────┬──────┬──────┬──────┐
Target I │                    │  IF  │  DE  │  EX  │  MEM │  WB  │
                              └──────┴──────┴──────┴──────┴──────┘
```

---

## Forwarding Mekanizması

### Forwarding Yolları

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                          FORWARDING YOLLARI                                      │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│                    PIPELINE STAGES                                               │
│   ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐      │
│   │  FETCH  │───▶│  DECODE │───▶│ EXECUTE │───▶│  MEMORY │───▶│WRITEBACK│      │
│   └─────────┘    └────┬────┘    └────┬────┘    └────┬────┘    └────┬────┘      │
│                       │              │              │               │           │
│                       │              │              │               │           │
│                       │      ┌───────┴───────┐     │               │           │
│                       │      │   ALU/CSR     │     │               │           │
│                       │      │   Result      │     │               │           │
│                       │      └───────────────┘     │               │           │
│                       │              ▲              │               │           │
│                       │              │              │               │           │
│   ┌───────────────────┼──────────────┼──────────────┼───────────────┘           │
│   │                   │              │              │                           │
│   │   WB → DE         │              │   MEM → EX   │   WB → EX                 │
│   │   Forwarding      │              │   Forwarding │   Forwarding              │
│   │   (fwd_a_de)      │              │   (fwd=10)   │   (fwd=01)                │
│   │   (fwd_b_de)      ▼              │              │                           │
│   │              ┌─────────┐         │              │                           │
│   │              │ rs1/rs2 │◀────────┴──────────────┘                           │
│   │              │   MUX   │                                                     │
│   │              └─────────┘                                                     │
│   │                                                                              │
│   └──────────────────────────────────────────────────────────────────────────────│
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### Execute Stage Forwarding (fwd_a_ex, fwd_b_ex)

```systemverilog
always_comb begin
    // Rs1 Forwarding - Execute Stage
    if (rf_rw_me_i && (r1_addr_ex_i == rd_addr_me_i) && (r1_addr_ex_i != 0)) begin
        // MEM stage'den forward (1 cycle önce)
        fwd_a_ex_o = 2'b10;
    end else if (rf_rw_wb_i && (r1_addr_ex_i == rd_addr_wb_i) && (r1_addr_ex_i != 0)) begin
        // WB stage'den forward (2 cycle önce)
        fwd_a_ex_o = 2'b01;
    end else begin
        // Normal register file okuma
        fwd_a_ex_o = 2'b00;
    end

    // Rs2 Forwarding - Execute Stage
    if (rf_rw_me_i && (r2_addr_ex_i == rd_addr_me_i) && (r2_addr_ex_i != 0)) begin
        // MEM stage'den forward
        fwd_b_ex_o = 2'b10;
    end else if (rf_rw_wb_i && (r2_addr_ex_i == rd_addr_wb_i) && (r2_addr_ex_i != 0)) begin
        // WB stage'den forward
        fwd_b_ex_o = 2'b01;
    end else begin
        // Normal register file okuma
        fwd_b_ex_o = 2'b00;
    end
end
```

### Forwarding Seçim Tablosu

| fwd_x_ex | Kaynak | Açıklama |
|----------|--------|----------|
| `2'b00` | Register File | Normal okuma, hazard yok |
| `2'b01` | WB Stage | 2 cycle önce yazılan değer |
| `2'b10` | MEM Stage | 1 cycle önce hesaplanan değer |

### Decode Stage Forwarding (fwd_a_de, fwd_b_de)

```systemverilog
always_comb begin
    // WB stage'den Decode'a forwarding
    fwd_a_de_o = rf_rw_wb_i && (r1_addr_de_i == rd_addr_wb_i) && (r1_addr_de_i != 0);
    fwd_b_de_o = rf_rw_wb_i && (r2_addr_de_i == rd_addr_wb_i) && (r2_addr_de_i != 0);
end
```

**Not**: Decode stage forwarding, branch kararları için gereklidir. Branch comparator decode aşamasında çalışır ve en güncel register değerlerine ihtiyaç duyar.

### Register x0 Koruması

```systemverilog
// x0 her zaman 0'dır, forwarding yapılmamalı
(r1_addr_ex_i != 0)  // x0 kontrolü
(r2_addr_ex_i != 0)  // x0 kontrolü
```

RISC-V mimarisinde `x0` register'ı hardwired 0'dır. Bu register'a yapılan yazımlar görmezden gelinir ve okumalar her zaman 0 döner. Bu nedenle, x0 için forwarding yapılmamalıdır.

---

## Stall Mekanizması

### Load-Use Hazard Tespiti

```systemverilog
always_comb begin
    // Load-use hazard: Load instruction sonucu hemen sonraki
    // instruction tarafından kullanılıyor
    lw_stall = rslt_sel_ex_0 && 
               ((r1_addr_de_i == rd_addr_ex_i) || (r2_addr_de_i == rd_addr_ex_i));
    
    // Stall sinyalleri
    stall_fe_o = lw_stall;  // Fetch'i durdur
    stall_de_o = lw_stall;  // Decode'u durdur
end
```

### Stall Koşulları

Load-use hazard aşağıdaki koşulların tümü sağlandığında oluşur:

1. **Execute aşamasında load instruction var**: `rslt_sel_ex_0 = 1`
2. **Decode aşamasındaki instruction, load'un hedefini okuyor**:
   - `r1_addr_de_i == rd_addr_ex_i` VEYA
   - `r2_addr_de_i == rd_addr_ex_i`

### Stall Davranışı

```
Load-Use Stall Sırası:
┌────────────────────────────────────────────────────────────────┐
│                                                                │
│  Cycle N:                                                      │
│  ┌─────────┐    ┌─────────┐    ┌─────────┐                    │
│  │   DE    │───▶│   EX    │───▶│   MEM   │                    │
│  │  ADD    │    │  LW x1  │    │   ...   │                    │
│  │ x2,x1,x3│    │  0(x4)  │    │         │                    │
│  └─────────┘    └─────────┘    └─────────┘                    │
│       │              │                                         │
│       │              ▼                                         │
│       │     ┌─────────────────┐                               │
│       └────▶│  Hazard Detect  │                               │
│             │  x1 == x1 ✓     │                               │
│             │  rslt_sel[0]=1 ✓│                               │
│             │  → lw_stall = 1 │                               │
│             └─────────────────┘                               │
│                                                                │
│  Cycle N+1: (Stall aktif)                                     │
│  ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐    │
│  │   DE    │    │ bubble  │───▶│   EX    │───▶│   MEM   │    │
│  │  ADD    │    │  (NOP)  │    │  LW x1  │    │   ...   │    │
│  │(bekliyor)    │         │    │(devam)  │    │         │    │
│  └─────────┘    └─────────┘    └─────────┘    └─────────┘    │
│       │                              │                         │
│       │                              ▼                         │
│       │                      ┌─────────────┐                  │
│       │                      │  x1 değeri  │                  │
│       │                      │   MEM'de    │                  │
│       └──────────────────────│  hazır oldu │                  │
│                              └─────────────┘                  │
│                                                                │
│  Cycle N+2: (Normal devam)                                    │
│  ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐    │
│  │   ...   │───▶│   DE    │───▶│   EX    │───▶│   MEM   │    │
│  │         │    │  ADD    │    │ bubble  │    │  LW x1  │    │
│  │         │    │ x2,x1,x3│    │         │    │         │    │
│  └─────────┘    └─────────┘    └─────────┘    └─────────┘    │
│                      │              ▲                         │
│                      │              │                         │
│                      │      ┌───────────────┐                 │
│                      └─────▶│ MEM→EX Forward│                 │
│                             │   fwd = 10    │                 │
│                             └───────────────┘                 │
│                                                                │
└────────────────────────────────────────────────────────────────┘
```

### Stall + Forward Kombinasyonu

Load-use hazard durumunda:
1. **Cycle 1**: Hazard tespit edilir, stall başlar
2. **Cycle 2**: Bubble eklenir, LW memory aşamasına ilerler
3. **Cycle 3**: MEM→EX forwarding ile değer aktarılır

---

## Flush Mekanizması

### Flush Koşulları

```systemverilog
always_comb begin
    // Branch misprediction: Decode stage flush
    flush_de_o = pc_sel_ex_i;  // Branch taken
    
    // Execute stage flush: Load-use stall VEYA branch misprediction
    flush_ex_o = lw_stall || pc_sel_ex_i;
end
```

### Flush Senaryoları

#### Senaryo 1: Branch Taken (Misprediction)

```
Cycle:     1      2      3      4      5      6
         ┌──────┬──────┬──────┬──────┬──────┐
BEQ      │  IF  │  DE  │  EX  │  MEM │  WB  │
         └──────┴──────┴──────┴──────┴──────┘
                              ↑
                              │ pc_sel_ex_i = 1 (branch taken)
                              │ flush_de_o = 1
                              │ flush_ex_o = 1
         
               ┌──────┬──────┐
Wrong I1 │     │  IF  │  DE  │ ← flush (NOP olur)
               └──────┴──────┘
                     ┌──────┐
Wrong I2       │     │  IF  │   ← flush (NOP olur)
                     └──────┘
                              ┌──────┬──────┬──────┬──────┬──────┐
Target   │                    │  IF  │  DE  │  EX  │  MEM │  WB  │
                              └──────┴──────┴──────┴──────┴──────┘
```

#### Senaryo 2: Load-Use Stall ile Flush

```
Cycle:     1      2      3      4      5      6
         ┌──────┬──────┬──────┬──────┬──────┐
LW x1    │  IF  │  DE  │  EX  │  MEM │  WB  │
         └──────┴──────┴──────┴──────┴──────┘
               ┌──────┬──────┬──────┬──────┬──────┐
ADD x2,x1│     │  IF  │  DE  │stall │  EX  │  MEM │
               └──────┴──────┴──────┴──────┴──────┘
                              ↑
                              │ lw_stall = 1
                              │ flush_ex_o = 1 (bubble inject)
                              │ stall_fe_o = 1
                              │ stall_de_o = 1
```

### Flush Öncelikleri

```
┌─────────────────────────────────────────────────────────────────┐
│                      FLUSH ÖNCELİK TABLOSU                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   Koşul                      │ flush_de │ flush_ex │ Açıklama  │
│   ───────────────────────────┼──────────┼──────────┼───────────│
│   lw_stall = 1, pc_sel = 0   │    0     │    1     │ Bubble    │
│   lw_stall = 0, pc_sel = 1   │    1     │    1     │ Br flush  │
│   lw_stall = 1, pc_sel = 1   │    1     │    1     │ Both      │
│   lw_stall = 0, pc_sel = 0   │    0     │    0     │ Normal    │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Karar Matrisi

### Tam Hazard Karar Tablosu

```
┌────────────────────────────────────────────────────────────────────────────────────────┐
│                              HAZARD KARAR MATRİSİ                                       │
├────────────────────────────────────────────────────────────────────────────────────────┤
│                                                                                        │
│  Girişler                                              Çıkışlar                        │
│  ──────────────────────────────────────────────────────────────────────────────────── │
│  rf_rw_me │ rs1_ex=rd_me │ rs1_ex≠0 │                    │ fwd_a_ex = 10 (MEM→EX)     │
│  rf_rw_wb │ rs1_ex=rd_wb │ rs1_ex≠0 │ (me koşulu yok)    │ fwd_a_ex = 01 (WB→EX)      │
│  diğer    │              │          │                    │ fwd_a_ex = 00 (RegFile)    │
│                                                                                        │
│  rf_rw_me │ rs2_ex=rd_me │ rs2_ex≠0 │                    │ fwd_b_ex = 10 (MEM→EX)     │
│  rf_rw_wb │ rs2_ex=rd_wb │ rs2_ex≠0 │ (me koşulu yok)    │ fwd_b_ex = 01 (WB→EX)      │
│  diğer    │              │          │                    │ fwd_b_ex = 00 (RegFile)    │
│                                                                                        │
│  rf_rw_wb │ rs1_de=rd_wb │ rs1_de≠0 │                    │ fwd_a_de = 1               │
│  rf_rw_wb │ rs2_de=rd_wb │ rs2_de≠0 │                    │ fwd_b_de = 1               │
│                                                                                        │
│  rslt_sel[0]=1 │ (rs1_de=rd_ex ∨ rs2_de=rd_ex)          │ lw_stall = 1               │
│                │                                         │ stall_fe = 1               │
│                │                                         │ stall_de = 1               │
│                │                                         │ flush_ex = 1               │
│                                                                                        │
│  pc_sel_ex = 1 │                                         │ flush_de = 1               │
│                │                                         │ flush_ex = 1               │
│                                                                                        │
└────────────────────────────────────────────────────────────────────────────────────────┘
```

### Forwarding Öncelik Sıralaması

```
┌─────────────────────────────────────────────────────────────────┐
│                  FORWARDING ÖNCELİK SIRASI                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   Öncelik 1: MEM Stage (fwd = 10)                              │
│   ────────────────────────────────                              │
│   En güncel değer, 1 cycle önce hesaplanan                      │
│   Koşul: rf_rw_me && (rs_ex == rd_me) && (rs_ex != 0)          │
│                                                                 │
│   Öncelik 2: WB Stage (fwd = 01)                               │
│   ───────────────────────────────                               │
│   2 cycle önce hesaplanan değer                                 │
│   Koşul: rf_rw_wb && (rs_ex == rd_wb) && (rs_ex != 0)          │
│          && !(MEM koşulu)                                       │
│                                                                 │
│   Öncelik 3: Register File (fwd = 00)                          │
│   ────────────────────────────────────                          │
│   Normal register okuma, hazard yok                             │
│   Koşul: Diğer durumlar                                         │
│                                                                 │
│   NOT: MEM önceliği daha yüksek çünkü aynı register'a          │
│        art arda yazılabilir. Bu durumda en son yazılan          │
│        değer (MEM stage'deki) doğru olandır.                    │
│                                                                 │
│   Örnek:                                                        │
│   ADD x1, x2, x3    ; x1'e yazar (şimdi WB'de)                 │
│   SUB x1, x4, x5    ; x1'e yazar (şimdi MEM'de)                │
│   OR  x6, x1, x7    ; x1'i okur → MEM'den forward              │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Zamanlama Diyagramları

### Normal İşlem (Hazard Yok)

```
clk     ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

         Cycle 1   Cycle 2   Cycle 3   Cycle 4   Cycle 5

Instr    ADD x1    SUB x5    OR x7     AND x9    XOR x11
         x2,x3     x6,x1     x8,x5     x10,x7    x12,x9

Stage    IF        DE        EX        MEM       WB
               │         │         │         │
fwd_a_ex ─────┴─────────┴─────────┴─────────┴───── 00
fwd_b_ex ─────────────────────────────────────────  00
stall    _____________________________________________  0
flush    _____________________________________________  0
```

### MEM→EX Forwarding

```
clk     ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

         Cycle 1   Cycle 2   Cycle 3   Cycle 4   Cycle 5

ADD x1   │ IF     │ DE      │ EX      │ MEM     │ WB
         │        │         │ result  │ fwd src │
         │        │         │  ready  │         │

SUB x2,x1│        │ IF      │ DE      │ EX      │ MEM
         │        │         │         │ x1 need │

fwd_a_ex ─────────────────────────────/‾‾‾‾‾‾‾‾‾‾‾‾\─────
                                      │   10      │

Pipeline │        │         │ x1=ALU  │─────────▶│ x1 to
Data Flow│        │         │ result  │ forward  │ SUB rs1
```

### Load-Use Hazard + Stall

```
clk     ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

         Cycle 1   Cycle 2   Cycle 3   Cycle 4   Cycle 5

LW x1    │ IF     │ DE      │ EX      │ MEM     │ WB
         │        │         │         │ x1 ready│

ADD x2,x1│        │ IF      │ DE(hold)│ DE      │ EX
         │        │         │ stall!  │ resume  │ fwd x1

lw_stall ─────────────────────/‾‾‾‾‾‾‾\________________________
                              │ detect │

stall_fe ─────────────────────/‾‾‾‾‾‾‾\________________________
stall_de ─────────────────────/‾‾‾‾‾‾‾\________________________
flush_ex ─────────────────────/‾‾‾‾‾‾‾\________________________

fwd_a_ex ───────────────────────────────────────/‾‾‾‾‾‾‾\──────
                                                │  10   │

Pipeline │        │         │ bubble  │ LW MEM  │ ADD EX
State    │        │         │ inject  │ x1 load │ x1 fwd
```

### Branch Misprediction + Flush

```
clk     ____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____/‾‾‾‾\____

         Cycle 1   Cycle 2   Cycle 3   Cycle 4   Cycle 5

BEQ taken│ IF     │ DE      │ EX      │ MEM     │ WB
         │        │         │ resolve │         │
         │        │         │ taken!  │         │

Wrong I1 │        │ IF      │ DE      │ FLUSH   │
         │        │(predict │(wrong)  │(bubble) │
         │        │ not-take)         │         │

Wrong I2 │        │         │ IF      │ FLUSH   │
         │        │         │(wrong)  │(bubble) │

Target   │        │         │         │ IF      │ DE
         │        │         │         │(correct)│(start)

pc_sel   ─────────────────────/‾‾‾‾‾‾‾\________________________
                              │taken=1│

flush_de ─────────────────────/‾‾‾‾‾‾‾\________________________
flush_ex ─────────────────────/‾‾‾‾‾‾‾\________________________
```

---

## Performans Analizi

### Hazard Etki Analizi

| Hazard Tipi | Gecikme | Çözüm | IPC Etkisi |
|-------------|---------|-------|------------|
| RAW (ALU→ALU) | 0 cycle | Forwarding | Yok |
| RAW (MEM→ALU) | 0 cycle | Forwarding | Yok |
| Load-Use | 1 cycle | Stall + Forward | ~%10-15 düşüş |
| Branch Mispred | 2 cycle | Flush | ~%5-10 düşüş |

### Forwarding Etkinliği

```
┌─────────────────────────────────────────────────────────────────┐
│                FORWARDING ETKİNLİK ANALİZİ                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   Forwarding Olmadan (Stall ile):                              │
│   ──────────────────────────────                                │
│   ADD x1, x2, x3    ; IF DE EX MEM WB                          │
│   SUB x4, x1, x5    ; IF DE -- -- EX MEM WB (3 cycle stall)    │
│                                                                 │
│   Forwarding ile:                                               │
│   ─────────────────                                             │
│   ADD x1, x2, x3    ; IF DE EX MEM WB                          │
│   SUB x4, x1, x5    ; IF DE EX MEM WB (0 cycle stall)          │
│                                                                 │
│   Kazanç: 3 cycle / instruction                                │
│                                                                 │
│   Load-Use (Kaçınılmaz):                                       │
│   ────────────────────                                          │
│   LW  x1, 0(x2)     ; IF DE EX MEM WB                          │
│   ADD x3, x1, x4    ; IF DE -- EX MEM WB (1 cycle stall)       │
│                                                                 │
│   Not: Load-use hazard tamamen çözülemez çünkü veri            │
│        memory'den MEM aşamasında gelir.                         │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### Stall İstatistikleri (Tipik Workload)

| Metrik | Değer | Açıklama |
|--------|-------|----------|
| Load oranı | ~25% | Tüm instruction'ların |
| Load-use oluşma | ~30% | Load'ların |
| Net stall oranı | ~7.5% | Toplam cycle'ların |
| Branch oranı | ~15% | Tüm instruction'ların |
| Misprediction | ~10% | Branch'lerin |
| Net flush oranı | ~3% | Toplam cycle'ların |

### Optimizasyon Önerileri

1. **Compiler Optimizasyonu**: Load-use hazard'ları için instruction scheduling
2. **Branch Prediction**: GSHARE, BTB, RAS ile misprediction azaltma
3. **Loop Unrolling**: Branch sayısını azaltma
4. **Prefetching**: Load gecikme gizleme

---

## Doğrulama ve Test

### Assertion'lar

```systemverilog
// MEM forwarding önceliği kontrolü
assert property (@(posedge clk_i)
    (rf_rw_me_i && rf_rw_wb_i && 
     (r1_addr_ex_i == rd_addr_me_i) && 
     (r1_addr_ex_i == rd_addr_wb_i) && 
     (r1_addr_ex_i != 0)) |->
    (fwd_a_ex_o == 2'b10)
) else $error("MEM forwarding should have priority over WB");

// x0 forwarding kontrolü
assert property (@(posedge clk_i)
    (r1_addr_ex_i == 0) |-> (fwd_a_ex_o == 2'b00)
) else $error("x0 should never be forwarded");

// Load-use stall kontrolü
assert property (@(posedge clk_i)
    (rslt_sel_ex_0 && (r1_addr_de_i == rd_addr_ex_i) && (rd_addr_ex_i != 0)) |->
    lw_stall
) else $error("Load-use hazard should trigger stall");

// Stall ve flush uyumu
assert property (@(posedge clk_i)
    lw_stall |-> (stall_fe_o && stall_de_o && flush_ex_o)
) else $error("Load-use stall signals inconsistent");
```

### Test Senaryoları

#### Test 1: Ardışık RAW Hazard

```assembly
# MEM→EX Forwarding Test
ADD x1, x2, x3      # x1'e yaz
SUB x4, x1, x5      # x1'i oku (1 cycle sonra)
# Beklenti: fwd_a_ex = 10, stall = 0

# WB→EX Forwarding Test
ADD x1, x2, x3      # x1'e yaz
NOP                 # 1 cycle boşluk
SUB x4, x1, x5      # x1'i oku (2 cycle sonra)
# Beklenti: fwd_a_ex = 01, stall = 0
```

#### Test 2: Load-Use Hazard

```assembly
# Load-Use Stall Test
LW  x1, 0(x2)       # x1'e load
ADD x3, x1, x4      # x1'i hemen kullan
# Beklenti: 1 cycle stall, sonra fwd_a_ex = 10
```

#### Test 3: Çoklu Yazma Aynı Register

```assembly
# Forwarding Priority Test
ADD x1, x2, x3      # x1'e yaz (WB'de olacak)
SUB x1, x4, x5      # x1'e tekrar yaz (MEM'de olacak)
OR  x6, x1, x7      # x1'i oku
# Beklenti: fwd_a_ex = 10 (MEM'den, en güncel değer)
```

#### Test 4: x0 Register

```assembly
# x0 Forwarding Prevention Test
ADD x0, x1, x2      # x0'a yaz (görmezden gelinir)
SUB x3, x0, x4      # x0'ı oku (her zaman 0)
# Beklenti: fwd_a_ex = 00, SUB rs1 = 0
```

#### Test 5: Branch Flush

```assembly
# Branch Misprediction Test
BEQ x1, x2, target  # Branch (tahmin: not-taken)
ADD x3, x4, x5      # Wrong path (flush edilmeli)
SUB x6, x7, x8      # Wrong path (flush edilmeli)
target:
AND x9, x10, x11    # Correct path
# Beklenti: flush_de = 1, flush_ex = 1
```

### Coverage Noktaları

```systemverilog
covergroup hazard_cg @(posedge clk);
    // Forwarding coverage
    fwd_a_type: coverpoint fwd_a_ex_o {
        bins no_fwd = {2'b00};
        bins wb_fwd = {2'b01};
        bins mem_fwd = {2'b10};
    }
    
    fwd_b_type: coverpoint fwd_b_ex_o {
        bins no_fwd = {2'b00};
        bins wb_fwd = {2'b01};
        bins mem_fwd = {2'b10};
    }
    
    // Stall coverage
    stall_type: coverpoint {stall_fe_o, stall_de_o} {
        bins no_stall = {2'b00};
        bins load_use = {2'b11};
    }
    
    // Flush coverage
    flush_type: coverpoint {flush_de_o, flush_ex_o} {
        bins no_flush = {2'b00};
        bins load_use_bubble = {2'b01};
        bins branch_flush = {2'b11};
    }
    
    // Cross coverage
    fwd_stall_cross: cross fwd_a_type, stall_type;
endgroup
```

---

## Özet

`hazard_unit` modülü, CERES RISC-V işlemcisinin doğru çalışması için kritik öneme sahip bir bileşendir:

### Temel İşlevler

1. **Data Forwarding**: MEM→EX, WB→EX, WB→DE yolları ile RAW hazard'ları çözer
2. **Stall Generation**: Load-use hazard'ları için 1 cycle stall üretir
3. **Flush Control**: Branch misprediction ve stall durumlarında pipeline temizler

### Tasarım Özellikleri

- **Tam Kombinasyonel**: Register içermez, minimum gecikme
- **Öncelikli Forwarding**: MEM > WB sıralaması
- **x0 Koruması**: Hardwired zero register forwarding yapılmaz
- **Minimal Stall**: Sadece load-use için zorunlu stall

### Performans Etkileri

- **Forwarding**: 3 cycle tasarruf (RAW hazard başına)
- **Load-Use Stall**: 1 cycle kayıp (kaçınılmaz)
- **Branch Flush**: 2 cycle kayıp (misprediction)

Bu modül, in-order 5-aşamalı pipeline için gerekli tüm hazard yönetimini sağlar ve işlemcinin tek cycle throughput'a ulaşmasını mümkün kılar.
