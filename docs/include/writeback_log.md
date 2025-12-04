# Writeback Log - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Spike Uyumlu Commit Trace](#spike-uyumlu-commit-trace)
3. [Log Formatları](#log-formatları)
4. [PASS/FAIL Algılama](#passfail-algılama)
5. [Konata Pipeline Trace](#konata-pipeline-trace)
6. [CSR Trace](#csr-trace)
7. [Kullanım ve Entegrasyon](#kullanım-ve-entegrasyon)

---

## Genel Bakış

### Amaç

`writeback_log.svh` dosyası, **Writeback stage** için kapsamlı trace ve log mekanizmalarını tanımlar. Özellikle **Spike simulator** ile karşılaştırılabilir commit trace formatı sağlar.

### Dosya Konumu

```
rtl/include/writeback_log.svh
```

### Temel Özellikler

| Özellik | Açıklama |
|---------|----------|
| **Spike Format** | `core 0: PC (INSTR) rd DATA` |
| **PASS/FAIL** | Otomatik test sonucu algılama |
| **Konata** | Pipeline visualizer desteği |
| **CSR Trace** | CSR register değişiklikleri |

---

## Spike Uyumlu Commit Trace

### Format Tanımı

Spike simulator'ün commit trace formatı:

```
core   0: 0x80000000 (0x00000297) x5  0x80000000
core   0: 0x80000004 (0x02028293) x5  0x80000028
core   0: 0x80000008 (0x30529073)
```

**Format:** `core <hart_id>: 0x<PC> (0x<INSTR>) [x<rd> 0x<DATA>]`

### Implementasyon

```systemverilog
`ifdef LOG_COMMIT

    // Spike-compatible commit trace
    always_ff @(posedge clk_i) begin
        if (commit_valid && !flush) begin
            if (rd_we && rd_addr != 5'd0) begin
                // Register write - show rd and value
                $display("core   0: 0x%08x (0x%08x) x%-2d 0x%08x",
                         commit_pc,
                         commit_instr,
                         rd_addr,
                         rd_data);
            end else begin
                // No register write (stores, branches, etc.)
                $display("core   0: 0x%08x (0x%08x)",
                         commit_pc,
                         commit_instr);
            end
        end
    end

`endif
```

### Spike Karşılaştırma

```bash
# RTL simülasyonu
make run T=rv32ui-p-add LOG_COMMIT=1 > rtl_trace.log

# Spike simülasyonu
spike --log-commits rv32ui-p-add > spike_trace.log

# Karşılaştırma
diff rtl_trace.log spike_trace.log
```

---

## Log Formatları

### Temel Commit Log

```systemverilog
`ifdef LOG_COMMIT
    always_ff @(posedge clk_i) begin
        if (commit_valid) begin
            // Standard format
            $display("core   0: 0x%08x (0x%08x) x%-2d 0x%08x",
                     pc, instr, rd, data);
        end
    end
`endif
```

### Genişletilmiş Log

```systemverilog
`ifdef LOG_COMMIT_VERBOSE

    always_ff @(posedge clk_i) begin
        if (commit_valid) begin
            // Instruction disassembly
            $display("[WB] PC=%08x %s rd=x%0d val=%08x",
                     pc,
                     disasm(instr),  // Disassembly function
                     rd,
                     data);

            // Memory operations
            if (is_load) begin
                $display("[WB]   LOAD addr=%08x data=%08x",
                         mem_addr, load_data);
            end
            if (is_store) begin
                $display("[WB]   STORE addr=%08x data=%08x",
                         mem_addr, store_data);
            end
        end
    end

`endif
```

### Memory Trace

```systemverilog
`ifdef LOG_MEM

    always_ff @(posedge clk_i) begin
        // Load commit
        if (load_commit) begin
            $display("MEM: LOAD  addr=%08x data=%08x size=%0d",
                     mem_addr, load_data, mem_size);
        end

        // Store commit
        if (store_commit) begin
            $display("MEM: STORE addr=%08x data=%08x size=%0d",
                     mem_addr, store_data, mem_size);
        end
    end

`endif
```

---

## PASS/FAIL Algılama

### RISC-V Test Signature

RISC-V testleri sonucu `tohost` adresine yazarak bildirir:

```systemverilog
// Test result detection
localparam TOHOST_ADDR = 32'h8000_1000;  // Configurable

`ifdef LOG_COMMIT

    always_ff @(posedge clk_i) begin
        // tohost write detection
        if (store_commit && mem_addr == TOHOST_ADDR) begin
            if (store_data == 32'h0000_0001) begin
                $display("*** PASS ***");
                $display("Test completed successfully @ %0t", $time);
                $finish(0);
            end else if (store_data != 32'h0) begin
                $display("*** FAIL ***");
                $display("Test failed with code: %0d @ %0t",
                         store_data >> 1, $time);
                $finish(1);
            end
        end
    end

`endif
```

### Benchmark Sonucu Algılama

```systemverilog
`ifdef SIM_UART_MONITOR

    // UART output monitoring
    string uart_buffer;

    always_ff @(posedge clk_i) begin
        if (uart_tx_valid) begin
            uart_buffer = {uart_buffer, string'(uart_tx_data)};

            // Check for PASS/FAIL patterns
            if (uart_buffer.find("PASS") != -1) begin
                $display("*** PASS detected in UART output ***");
                $finish(0);
            end
            if (uart_buffer.find("FAIL") != -1) begin
                $display("*** FAIL detected in UART output ***");
                $finish(1);
            end

            // CoreMark result pattern
            if (uart_buffer.find("CoreMark 1.0 :") != -1) begin
                $display("*** CoreMark completed ***");
            end
        end
    end

`endif
```

### Write to TOHOST Detection

```systemverilog
// Detailed tohost analysis
always_ff @(posedge clk_i) begin
    if (store_commit && mem_addr == TOHOST_ADDR) begin
        case (store_data)
            32'h0000_0001: begin
                $display("[TEST] PASS @ cycle %0d", cycle_count);
            end
            32'h0000_0000: begin
                // Ignore zero write
            end
            default: begin
                // Fail with test number
                $display("[TEST] FAIL test_num=%0d @ cycle %0d",
                         store_data >> 1, cycle_count);
            end
        endcase
    end
end
```

---

## Konata Pipeline Trace

### Konata Format

Konata pipeline visualizer için özel trace format:

```systemverilog
`ifdef KONATA_TRACER

    integer konata_file;

    initial begin
        konata_file = $fopen("pipeline.log", "w");
        $fwrite(konata_file, "Kanata\t0004\n");
    end

    always_ff @(posedge clk_i) begin
        // Instruction fetch
        if (if_valid) begin
            $fwrite(konata_file, "I\t%0d\t%0d\t0\n",
                    instr_id, cycle_count);
        end

        // Stage transitions
        if (id_valid) begin
            $fwrite(konata_file, "S\t%0d\t%0d\t%s\n",
                    instr_id, cycle_count, "D");
        end

        if (ex_valid) begin
            $fwrite(konata_file, "S\t%0d\t%0d\t%s\n",
                    instr_id, cycle_count, "E");
        end

        if (mem_valid) begin
            $fwrite(konata_file, "S\t%0d\t%0d\t%s\n",
                    instr_id, cycle_count, "M");
        end

        // Instruction commit
        if (commit_valid) begin
            $fwrite(konata_file, "R\t%0d\t%0d\t0\n",
                    instr_id, cycle_count);
        end

        // Instruction flush
        if (flush_valid) begin
            $fwrite(konata_file, "R\t%0d\t%0d\t1\n",
                    instr_id, cycle_count);
        end
    end

    final begin
        $fclose(konata_file);
    end

`endif
```

### Konata Komutları

| Komut | Format | Açıklama |
|-------|--------|----------|
| I | `I id cycle 0` | Instruction issue |
| S | `S id cycle stage` | Stage transition |
| R | `R id cycle flush` | Retire (0=commit, 1=flush) |
| L | `L id cycle text` | Label (optional) |

---

## CSR Trace

### CSR Write Logging

```systemverilog
`ifdef LOG_CSR

    always_ff @(posedge clk_i) begin
        if (csr_we) begin
            $display("[CSR] WRITE %s (0x%03x) = 0x%08x @ PC=%08x",
                     csr_name(csr_addr),
                     csr_addr,
                     csr_wdata,
                     commit_pc);
        end
    end

    function automatic string csr_name(input logic [11:0] addr);
        case (addr)
            12'h300: return "mstatus";
            12'h301: return "misa";
            12'h304: return "mie";
            12'h305: return "mtvec";
            12'h340: return "mscratch";
            12'h341: return "mepc";
            12'h342: return "mcause";
            12'h343: return "mtval";
            12'h344: return "mip";
            12'hF11: return "mvendorid";
            12'hF12: return "marchid";
            12'hF13: return "mimpid";
            12'hF14: return "mhartid";
            12'hB00: return "mcycle";
            12'hB02: return "minstret";
            default: return $sformatf("csr_%03x", addr);
        endcase
    endfunction

`endif
```

### Exception/Interrupt Logging

```systemverilog
`ifdef LOG_EXCEPTION

    always_ff @(posedge clk_i) begin
        if (exception_valid) begin
            $display("[TRAP] EXCEPTION cause=%s (%0d) PC=%08x tval=%08x",
                     exception_name(mcause),
                     mcause,
                     mepc,
                     mtval);
        end

        if (interrupt_valid) begin
            $display("[TRAP] INTERRUPT cause=%0d PC=%08x",
                     mcause[30:0],
                     mepc);
        end

        if (mret_valid) begin
            $display("[TRAP] MRET return to PC=%08x",
                     mepc);
        end
    end

`endif
```

---

## Kullanım ve Entegrasyon

### Makefile Entegrasyonu

```makefile
# Log kontrolleri
LOG_COMMIT ?= 0
LOG_CSR ?= 0
LOG_MEM ?= 0
KONATA_TRACER ?= 0

# Verilator defines
ifeq ($(LOG_COMMIT),1)
    VFLAGS += +define+LOG_COMMIT
endif

ifeq ($(KONATA_TRACER),1)
    VFLAGS += +define+KONATA_TRACER +define+COMMIT_TRACER
endif
```

### Kullanım Örnekleri

```bash
# ISA test with commit trace
make run T=rv32ui-p-add LOG_COMMIT=1

# Pipeline visualization
make run T=rv32ui-p-add KONATA_TRACER=1

# Full debug mode
make run T=test LOG_COMMIT=1 LOG_CSR=1 LOG_MEM=1

# Benchmark with UART monitoring
make cm SIM_UART_MONITOR=1 LOG_COMMIT=1
```

### Log Dosyaları

| Log | Dosya | İçerik |
|-----|-------|--------|
| Commit | stdout/commit.log | Spike-uyumlu trace |
| Pipeline | pipeline.log | Konata format |
| UART | uart.log | UART çıktısı |

---

## Performans Etkisi

### Log Overhead

| Mode | Overhead | Kullanım |
|------|----------|----------|
| No logging | 0% | Production |
| LOG_COMMIT | ~5% | Debug |
| KONATA_TRACER | ~10% | Pipeline analysis |
| All logs | ~20% | Full debug |

### SIM_FAST Mode

```systemverilog
`ifdef SIM_FAST
    // Tüm log'lar devre dışı
    // Maksimum simülasyon hızı
`else
    // Normal log modları aktif
`endif
```

---

## Özet

`writeback_log.svh` dosyası:

1. **Spike Format**: `core 0: PC (INSTR) rd DATA`
2. **PASS/FAIL**: tohost ve UART izleme
3. **Konata**: Pipeline visualizer desteği
4. **CSR Trace**: Register değişiklikleri
5. **Configurable**: Makefile ile kontrol

Bu dosya, CERES RISC-V işlemcisinin doğrulama ve debug altyapısının temelini oluşturur.
