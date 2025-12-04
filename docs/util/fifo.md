# FIFO Modülleri - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [count_fifo](#count_fifo)
3. [le_fifo](#le_fifo)
4. [wbit_fifo](#wbit_fifo)
5. [Karşılaştırma](#karşılaştırma)
6. [Kullanım Örnekleri](#kullanım-örnekleri)

---

## Genel Bakış

### Amaç

`fifo.sv` dosyası, farklı implementasyon stratejilerine sahip **üç FIFO modülü** içerir. Her biri farklı alan/performans trade-off'larına sahiptir.

### Dosya Konumu

```
rtl/util/fifo.sv
```

### FIFO Tipleri

| Modül | Full/Empty Algılama | Alan | Performans |
|-------|---------------------|------|------------|
| `count_fifo` | Counter-based | Orta | Hızlı |
| `le_fifo` | Pointer comparison | Düşük | Orta |
| `wbit_fifo` | Wrap bit | Düşük | Hızlı |

---

## count_fifo

### Açıklama

Counter tabanlı FIFO. Ayrı bir `fifo_count` sayacı ile full/empty durumlarını takip eder.

### Modül Arayüzü

```systemverilog
module count_fifo #(
    parameter DATA_WIDTH = 8,
    parameter FIFO_DEPTH = 4
) (
    input  logic                    clk,
    input  logic                    rst,
    input  logic                    write_en,
    input  logic                    read_en,
    input  logic [DATA_WIDTH-1:0]   write_data,
    output logic [DATA_WIDTH-1:0]   read_data,
    output logic                    full,
    output logic                    empty
);
```

### Çalışma Prensibi

```systemverilog
// Ayrı counter ile eleman sayısı takibi
logic [ADDR_WIDTH:0] fifo_count;

always_ff @(posedge clk) begin
    if (rst) begin
        fifo_count <= 0;
    end else begin
        case ({write_en, read_en})
            2'b10:   fifo_count <= fifo_count + 1;  // Write only
            2'b01:   fifo_count <= fifo_count - 1;  // Read only
            default: fifo_count <= fifo_count;       // Both or neither
        endcase
    end
end

assign full  = (fifo_count == FIFO_DEPTH);
assign empty = (fifo_count == 0);
```

### Avantajlar/Dezavantajlar

| Avantaj | Dezavantaj |
|---------|------------|
| Basit full/empty logic | Ekstra counter register |
| Eleman sayısı bilinir | Daha fazla flip-flop |
| Hızlı hesaplama | - |

---

## le_fifo

### Açıklama

Pointer karşılaştırması tabanlı FIFO. Full durumu `(write_ptr + 1) == read_ptr` ile algılanır (bir slot boş bırakılır).

### Modül Arayüzü

```systemverilog
module le_fifo #(
    parameter DATA_WIDTH = 8,
    parameter FIFO_DEPTH = 4
) (
    input  logic                    clk,
    input  logic                    rst,
    input  logic                    write_en,
    input  logic                    read_en,
    input  logic [DATA_WIDTH-1:0]   write_data,
    output logic [DATA_WIDTH-1:0]   read_data,
    output logic                    full,
    output logic                    empty
);
```

### Çalışma Prensibi

```systemverilog
logic [ADDR_WIDTH-1:0] write_ptr, read_ptr;

// Full: bir sonraki yazma pozisyonu = okuma pozisyonu
assign full  = ((write_ptr + 1'b1) == read_ptr);

// Empty: yazma ve okuma pozisyonu aynı
assign empty = (write_ptr == read_ptr);
```

### Dezavantaj

**Kapasite Kaybı**: FIFO_DEPTH=4 iken sadece 3 eleman depolanabilir çünkü bir slot full/empty ayrımı için boş bırakılır.

```
   Full durumu:
   ┌───┬───┬───┬───┐
   │ D │ D │ D │   │  ← Bir slot her zaman boş
   └───┴───┴───┴───┘
     ↑           ↑
   read_ptr   write_ptr
```

---

## wbit_fifo

### Açıklama

Wrap bit tabanlı FIFO. Pointer'lara ekstra bir MSB (wrap bit) eklenerek full/empty durumları ayrılır. **Tüm kapasiteyi kullanır**.

### Modül Arayüzü

```systemverilog
module wbit_fifo #(
    parameter DATA_WIDTH = 8,
    parameter FIFO_DEPTH = 4
) (
    input  logic                    clk,
    input  logic                    rst,
    input  logic                    write_en,
    input  logic                    read_en,
    input  logic [DATA_WIDTH-1:0]   write_data,
    output logic [DATA_WIDTH-1:0]   read_data,
    output logic                    full,
    output logic                    empty
);
```

### Çalışma Prensibi

```systemverilog
// Pointer'lar ADDR_WIDTH+1 bit (wrap bit dahil)
logic [ADDR_WIDTH:0] write_ptr, read_ptr;

// Wrap bit: MSB farklı mı?
assign wrap_around = (write_ptr[ADDR_WIDTH] ^ read_ptr[ADDR_WIDTH]);

// Full: wrap bit farklı VE alt bitler aynı
assign full = wrap_around & (write_ptr[ADDR_WIDTH-1:0] == read_ptr[ADDR_WIDTH-1:0]);

// Empty: tüm bitler aynı
assign empty = (write_ptr == read_ptr);

// Bellek adresleme: sadece alt bitler
always_ff @(posedge clk) begin
    if (write_en && !full) begin
        fifo_mem[write_ptr[ADDR_WIDTH-1:0]] <= write_data;
        write_ptr <= write_ptr + 1;
    end
end
```

### Wrap Bit Diyagramı

```
FIFO_DEPTH = 4 (2-bit address)
Pointer = 3-bit [wrap_bit : addr]

Empty:  write_ptr = 000, read_ptr = 000  (aynı)
        write_ptr = 100, read_ptr = 100  (aynı)

Full:   write_ptr = 100, read_ptr = 000  (wrap farklı, addr aynı)
        write_ptr = 000, read_ptr = 100  (wrap farklı, addr aynı)

Normal: write_ptr = 010, read_ptr = 000  (2 eleman)
        write_ptr = 111, read_ptr = 101  (2 eleman, wrap olmuş)
```

### Avantajlar

| Avantaj | Açıklama |
|---------|----------|
| Tam kapasite | Tüm FIFO_DEPTH slot kullanılır |
| Basit logic | Sadece XOR ve karşılaştırma |
| Counter yok | Ekstra register gerekmez |

---

## Karşılaştırma

### Kaynak Kullanımı

| Modül | Registers | Logic | Kapasite |
|-------|-----------|-------|----------|
| `count_fifo` | N+1 bit | Adder | DEPTH |
| `le_fifo` | N bit | Comparator | DEPTH-1 |
| `wbit_fifo` | N+1 bit | XOR+Comparator | DEPTH |

### Full/Empty Timing

| Modül | Full Path | Empty Path |
|-------|-----------|------------|
| `count_fifo` | counter → compare | counter → compare |
| `le_fifo` | add → compare | compare |
| `wbit_fifo` | XOR → AND → compare | compare |

### Kullanım Senaryoları

| Senaryo | Önerilen |
|---------|----------|
| Eleman sayısı gerekli | `count_fifo` |
| Minimum alan | `le_fifo` (1 slot kayıp tolere edilebilir) |
| Tam kapasite + düşük alan | `wbit_fifo` |

---

## Kullanım Örnekleri

### UART TX FIFO

```systemverilog
wbit_fifo #(
    .DATA_WIDTH(8),
    .FIFO_DEPTH(256)
) u_uart_tx_fifo (
    .clk       (clk_i),
    .rst       (!rst_ni),
    .write_en  (tx_write),
    .read_en   (tx_read),
    .write_data(tx_data_in),
    .read_data (tx_data_out),
    .full      (tx_fifo_full),
    .empty     (tx_fifo_empty)
);
```

### Pipeline Buffer

```systemverilog
count_fifo #(
    .DATA_WIDTH(64),
    .FIFO_DEPTH(4)
) u_pipe_buffer (
    .clk       (clk_i),
    .rst       (!rst_ni),
    .write_en  (producer_valid && !full),
    .read_en   (consumer_ready && !empty),
    .write_data(producer_data),
    .read_data (consumer_data),
    .full      (full),
    .empty     (empty)
);
```

---

## Özet

FIFO modülleri:

1. **count_fifo**: Counter ile eleman takibi
2. **le_fifo**: Pointer karşılaştırması (1 slot kayıp)
3. **wbit_fifo**: Wrap bit ile tam kapasite

Uygulama gereksinimlerine göre uygun FIFO seçilmelidir.
