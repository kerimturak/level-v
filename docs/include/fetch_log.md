# Fetch Log - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Log Formatı](#log-formatı)
3. [Sinyaller](#sinyaller)
4. [Kullanım](#kullanım)
5. [Debug Senaryoları](#debug-senaryoları)

---

## Genel Bakış

### Amaç

`fetch_log.svh` dosyası, **Fetch stage** debug ve trace çıktıları için log formatlarını tanımlar. I-Cache erişimleri, branch prediction sonuçları ve pipeline stall'ları izlenebilir.

### Dosya Konumu

```
rtl/include/fetch_log.svh
```

### Aktivasyon

```bash
# Makefile ile
make run T=test LOG_FETCH=1

# Verilator define
+define+LOG_FETCH
```

---

## Log Formatı

### Temel Log Yapısı

```systemverilog
`ifdef LOG_FETCH

    // Fetch trace output
    always_ff @(posedge clk_i) begin
        if (fetch_valid && !stall) begin
            $display("[FETCH] PC=%08x INSTR=%08x %s @ %0t",
                     pc,
                     instruction,
                     is_compressed ? "C" : "I",
                     $time);
        end
    end

`endif
```

### Örnek Çıktı

```
[FETCH] PC=80000000 INSTR=00000297 I @ 1000
[FETCH] PC=80000004 INSTR=02028293 I @ 1010
[FETCH] PC=80000008 INSTR=00010137 I @ 1020
[FETCH] PC=8000000c INSTR=f1402573 I @ 1030
[FETCH] PC=80000010 INSTR=30200073 I @ 1040
```

---

## Sinyaller

### İzlenen Sinyaller

```systemverilog
// Fetch stage signals
logic [31:0] pc;              // Current program counter
logic [31:0] instruction;     // Fetched instruction
logic        fetch_valid;     // Fetch successful
logic        is_compressed;   // Compressed instruction
logic        stall;           // Pipeline stall
logic        flush;           // Pipeline flush

// I-Cache signals
logic        icache_hit;      // Cache hit
logic        icache_miss;     // Cache miss
logic        icache_busy;     // Cache busy

// Branch prediction
logic        bp_taken;        // Predicted taken
logic [31:0] bp_target;       // Predicted target
```

### Log Seviyeleri

```systemverilog
// Basic fetch log
`ifdef LOG_FETCH
    // PC, instruction logging
`endif

// Verbose fetch log
`ifdef LOG_FETCH_VERBOSE
    // Cache hit/miss
    // Branch prediction details
    // Stall reasons
`endif
```

---

## Kullanım

### Basit Fetch Log

```systemverilog
`include "fetch_log.svh"

module fetch_stage
  import ceres_param::*;
(
    input  logic        clk_i,
    // ...
);

`ifdef LOG_FETCH
    always_ff @(posedge clk_i) begin
        if (o_valid) begin
            $display("[FETCH] PC=%08x INSTR=%08x @ %0t",
                     o_pc, o_instr, $time);
        end
    end
`endif

endmodule
```

### Detaylı Fetch Log

```systemverilog
`ifdef LOG_FETCH_VERBOSE

    always_ff @(posedge clk_i) begin
        // Cache durumu
        if (icache_req) begin
            if (icache_hit) begin
                $display("[FETCH] ICACHE HIT  PC=%08x @ %0t", pc, $time);
            end else begin
                $display("[FETCH] ICACHE MISS PC=%08x @ %0t", pc, $time);
            end
        end

        // Branch prediction
        if (bp_valid) begin
            $display("[FETCH] BP %s target=%08x @ %0t",
                     bp_taken ? "TAKEN" : "NOT_TAKEN",
                     bp_target, $time);
        end

        // Stall nedeni
        if (stall) begin
            $display("[FETCH] STALL reason=%s @ %0t",
                     stall_reason.name(), $time);
        end

        // Flush
        if (flush) begin
            $display("[FETCH] FLUSH redirect=%08x @ %0t",
                     redirect_pc, $time);
        end
    end

`endif
```

---

## Debug Senaryoları

### 1. I-Cache Miss Analizi

```systemverilog
// Cache miss sayısını takip et
`ifdef LOG_FETCH
    int icache_miss_count = 0;
    int icache_hit_count = 0;

    always_ff @(posedge clk_i) begin
        if (icache_req) begin
            if (icache_hit) begin
                icache_hit_count <= icache_hit_count + 1;
            end else begin
                icache_miss_count <= icache_miss_count + 1;
                $display("[FETCH] MISS #%0d PC=%08x @ %0t",
                         icache_miss_count, pc, $time);
            end
        end
    end

    final begin
        $display("[FETCH] Total: Hits=%0d Misses=%0d Rate=%.2f%%",
                 icache_hit_count, icache_miss_count,
                 100.0 * icache_hit_count / (icache_hit_count + icache_miss_count));
    end
`endif
```

### 2. Branch Misprediction

```systemverilog
`ifdef LOG_FETCH
    always_ff @(posedge clk_i) begin
        if (branch_resolve) begin
            if (bp_mispredicted) begin
                $display("[FETCH] MISPREDICT PC=%08x pred=%08x actual=%08x @ %0t",
                         branch_pc, bp_target, actual_target, $time);
            end
        end
    end
`endif
```

### 3. Pipeline Stall İzleme

```systemverilog
`ifdef LOG_FETCH
    int stall_cycles = 0;

    always_ff @(posedge clk_i) begin
        if (stall) begin
            stall_cycles <= stall_cycles + 1;
            if (stall_cycles > 100) begin
                $warning("[FETCH] Long stall: %0d cycles @ %0t",
                         stall_cycles, $time);
            end
        end else begin
            if (stall_cycles > 0) begin
                $display("[FETCH] Stall ended after %0d cycles @ %0t",
                         stall_cycles, $time);
            end
            stall_cycles <= 0;
        end
    end
`endif
```

---

## İlgili Dosyalar

| Dosya | Açıklama |
|-------|----------|
| `rtl/core/stage01_fetch/` | Fetch stage modülleri |
| `rtl/core/mmu/cache.sv` | I-Cache implementasyonu |
| `writeback_log.svh` | Commit trace (karşılaştırma için) |

---

## Özet

`fetch_log.svh` dosyası:

1. **PC/Instruction Log**: Temel fetch izleme
2. **Cache Analysis**: Hit/miss istatistikleri
3. **Branch Debug**: Misprediction izleme
4. **Stall Analysis**: Pipeline stall nedenleri
5. **Conditional Compilation**: `ifdef` ile kontrol

Bu dosya, fetch stage debug ve performans analizi için kullanılır.
