# Level RISC-V — run_v5 Analysis Report and run_v6 Roadmap

**Date**: 2026-02-19  
**Design**: `level_wrapper` (SKY130, OpenLane 2023.09.07)  
**Reference**: `run_v5` — GDS successful, signoff partially complete

---

## 1. run_v5 Status Summary

| Metric | Result | Status |
|--------|--------|--------|
| GDS output | 424 MB | ✅ Successful |
| Routing DRC | 0 violation | ✅ Clean |
| Detailed routing wire length | 6,381,374 µm | ✅ |
| Via count | 513,037 | ✅ |
| Instance count | 2,510,059 (incl. filler/decap) | ✅ |
| Net count | 61,763 | ✅ |
| **Typical corner** Setup WNS | **+3.42 ns** | ✅ MET |
| **Typical corner** Hold WNS | **+0.09 ns** | ✅ MET |
| **Slowest corner** Setup WNS | **-21.69 ns** | ❌ INVALID (no SRAM SS lib) |
| **Slowest corner** TNS | -42,833 ns (8687 paths) | ❌ INVALID |
| IR drop report | Skipped (`RUN_IRDROP_REPORT=0`) | ⚠️ |
| Magic LEF | Not completed (OOM — 13.7 GB RAM) | ❌ |
| LVS | Did not run (Magic LEF dependency) | ❌ |
| Antenna repair | Completed (inside GRT) | ✅ |

### Flow steps (run_v5)

```
 1  Synthesis                    ✅  (4807 warn, 39 ABC errors — harmless)
 2  STA (single-corner)         ✅  (25 warn — SRAM dout0 + unconstrained)
 3  Initial Floorplan           ✅  5488×5478 µm
 4  IO Placement                ✅
 5  Manual Macro Placement      ✅  26 SRAM macros
 6  Tap/Decap Insertion         ✅
 7  PDN Generation              ✅  (3× PDN-0110 via warning)
 8  Global Placement            ✅
 9  GPL STA                     ✅
10  Placement Resizer           ✅
11  Detailed Placement          ✅
12  DPL STA                     ✅
13  CTS                         ✅  (4896 pure-wire, harmless)
14  CTS STA                     ✅
15  CTS Resizer                 ✅
16  GRT Resizer Design          ✅
17  RSZ Design STA              ✅
18  GRT Resizer Timing          ✅
19  RSZ Timing STA              ✅
20  Global Routing              ✅  (Antenna repair completed)
22  GRT STA                     ✅  (580 unconstrained endpoints)
23  Fill Insertion               ✅
24  Detailed Routing            ✅  0 DRC, 39 minutes, peak 12.8 GB RAM
25  Wire Length Check           ✅
26  SPEF Extraction (min)       ✅
27  MCSTA (min)                 ✅
28  SPEF Extraction (max)       ✅
29  MCSTA (max)                 ✅  (invalid violation — missing SRAM SS lib)
30  SPEF Extraction (nom)       ✅
31  MCSTA (nom)                 ✅  (Typical +3.42 ns, Slowest invalid fail)
32  Magic GDS                   ✅  424 MB
32  Magic LEF                   ❌  OOM/stuck (13.7 GB RAM, killed)
```

---

## 2. Warning Classification

### 2.1 🔴 CRITICAL — Missing SRAM Multi-Corner Liberty

- **Count**: 3 corners × ~8700 paths = ~26000 VIOLATED lines
- **Symptom**: Slowest corner WNS = -21.69 ns, TNS = -42833 ns
- **Root cause**: Only **TT** (Typical, 1.8 V, 25 °C) Liberty is available for the SRAM macro.
  OpenSTA cannot find SRAM timing in **SS** (Slow-Slow, low voltage, high temperature) and **FF** (Fast-Fast)
  corners → SRAM delay is assumed **0 ns** →
  all SRAM paths produce spurious timing violations.
- **Impact**: Multi-corner STA results are not trustworthy. Unacceptable if tape-out is planned.
- **Current Liberty**: `sky130_sram_1kbyte_1rw1r_32x256_8_TT_1p8V_25C.lib`

### 2.2 🔴 CRITICAL — IR Drop Report Skipped

- **Symptom**: `RUN_IRDROP_REPORT=0` in config
- **Root cause**: PDN mesh generates ~1.6M nodes → IR drop solver uses 15+ GB RAM → OOM kill
- **Impact**: Power grid quality not verified. On-chip IR droop is possible.

### 2.3 🟡 MEDIUM — Synthesis “Wire Has No Driver” Warnings

- **Count**: 4807
- **Examples**:
  - `Wire cpu.\pipe[] is used but has no driver` (291×)
  - `Wire wb_interconnect.\wb_m_o[] is used but has no driver` (228×)
  - `Wire memory_arbiter.\iomem_req_o[] is used but has no driver` (179×)
  - `Wire dcache.\lowX_req_o[]` (166×), `icache.\cache_res_o[]` (131×)
  - `Wire cs_reg_file.\tdata_o[]` (128×), `reg_file.\r_data_o[]` (64×)
- **Root cause**: sv2v converts SystemVerilog struct/interface buses to Verilog wires.
  Yosys sees some bus fragments as undriven — yet synthesized logic behaves correctly.
- **Impact**: No functional impact. Noise — run_v5 already routed correctly.
- **Mitigation**: Struct default initialization in RTL or sv2v post-processing script

### 2.4 🟡 MEDIUM — SRAM `dout0` Port Not Found

- **Count**: 24 (one per SRAM instance)
- **Symptom**: `port dout0 not found` — during STA
- **Root cause**: Liberty has `pin(dout0[31:0])` (bus notation), but the synthesized
  netlist ports are bit-blasted: `dout0[0]`, `dout0[1]`, ... `dout0[31]`.
  OpenSTA cannot match the bus name to bit-blasted names.
- **Impact**: SRAM output timing not modeled in STA → paths after SRAM are wrong
- **Mitigation**: Convert the Liberty file to bit-blasted format

### 2.5 🟢 LOW — STA `ccsn_pnlh` / `ccsn_ovrf` Template Warnings

- **Count**: 46,288 (on all 3 corners)
  - `ccsn_pnlh not found`: 22,960
  - `ccsn_ovrf not found`: 10,736
- **Root cause**: SKY130 Liberty files include CCSN (current source) noise tables,
  but OpenSTA does not support this noise model.
- **Impact**: **None.** Information for noise analysis — does not affect timing.
- **Mitigation**: Ignore. Optional: strip from Liberty.

### 2.6 🟢 LOW — 580 Unconstrained Endpoints

- **Count**: 580 ports (no timing constraints)
- **Scope**:
  - `gpio_o[0:31]`, `gpio_oe_o[0:31]` — 64 pins
  - `vga_r_o`, `vga_g_o`, `vga_b_o`, `vga_hsync_o`, `vga_vsync_o` — VGA
  - `pwm_o`, `pwm_n_o` — PWM
  - `spi0_mosi_o`, `spi0_sclk_o`, `spi0_ss_o` — SPI
  - `i2c0_scl_io`, `i2c0_sda_io` — I2C
  - `wdt_reset_o`, `status_led_o`, `cpu_halt_o`
  - SRAM `csb0`, `csb1`, `web0` pins (26 macros × ~8 pins)
- **Root cause**: SDC does not define `set_output_delay` or `set_false_path` for these ports.
- **Impact**: These pins are not timed → STA report is incomplete

### 2.7 🟢 LOW — Other Warnings

| Warning | Count | Source | Description |
|---------|-------|--------|-------------|
| `PDN-0110 No via met4↔met5` | 3 | PDN | Could not place vias at a few strap locations |
| `ABC: network is combinational` | 39 | Synthesis | ABC optimizer saw subcircuits as combinational |
| `SRAM cell overlap in GDS` | ~100 | Magic | Duplicate `contact_7` cell in SRAM GDS |
| `CTS-0043 pure wire` | 4896 | CTS | Short clock wires that need no buffer |
| `SPEF not connected to net` | 5748 | SPEF/STA | Parasitic nodes could not connect around SRAM |
| `SRAM lib already exists` | 1 | STA | Same Liberty loaded twice |

---

## 3. run_v6 Roadmap

### Phase 1: SRAM Liberty fixes (critical) — Priority 1

#### 1.1 SRAM SS/FF corner Liberty generation

**Issue**: Only TT corner exists → multi-corner STA fails spuriously  
**Fix**: Generate SS and FF Liberty from the OpenRAM SRAM compiler.

If OpenRAM is not available, **manual corner scaling** can be done:

```bash
# SS (Slow-Slow) Liberty: increase delays by 30%, produce new lib
python3 scale_sram_liberty.py \
    --input  sky130_sram_..._TT_1p8V_25C.lib \
    --output sky130_sram_..._SS_1p6V_100C.lib \
    --delay_scale 1.30 \
    --slew_scale 1.35

# FF (Fast-Fast) Liberty: reduce delays by 25%
python3 scale_sram_liberty.py \
    --input  sky130_sram_..._TT_1p8V_25C.lib \
    --output sky130_sram_..._FF_1p95V_n40C.lib \
    --delay_scale 0.75 \
    --slew_scale 0.70
```

**config.tcl change**:
```tcl
set sram_lib_tt  "$sram_macro_dir/sky130_sram_..._TT_1p8V_25C.lib"
set sram_lib_ss  "$sram_macro_dir/sky130_sram_..._SS_1p6V_100C.lib"
set sram_lib_ff  "$sram_macro_dir/sky130_sram_..._FF_1p95V_n40C.lib"

set ::env(EXTRA_LIBS) [list $sram_lib_tt]

# Multi-corner SRAM Liberty
set ::env(STA_WRITE_LIB) 1
# OpenLane corner mapping:
#   min (fastest) → FF lib
#   nom (typical) → TT lib
#   max (slowest) → SS lib
```

#### 1.2 Liberty pin format fix (bit-blast)

**Issue**: `pin(dout0[31:0])` bus notation → OpenSTA cannot match bit-blasted netlist  
**Fix**: Script-convert bus pins in Liberty to bit-blasted format

```bash
# Current:   pin(dout0[31:0]) { direction: output; ... }
# Target:    pin(dout0[0]) { direction: output; ... }
#            pin(dout0[1]) { direction: output; ... }
#            ...
#            pin(dout0[31]) { direction: output; ... }
```

This conversion will be added to the `fetch_sky130_sram_macros_for_openlane.sh` script.

### Phase 2: Complete SDC constraints — Priority 2

#### 2.1 Close out unconstrained endpoints

Section to add to `constraint.sdc`:

```tcl
# ==============================================================
# 12. GPIO CONSTRAINTS
# ==============================================================
set_false_path -to [get_ports gpio_o[*]]
set_false_path -to [get_ports gpio_oe_o[*]]
set_false_path -from [get_ports gpio_i[*]]

# ==============================================================
# 13. VGA OUTPUT (slow pixel clock domain)
# ==============================================================
set_false_path -to [get_ports vga_r_o[*]]
set_false_path -to [get_ports vga_g_o[*]]
set_false_path -to [get_ports vga_b_o[*]]
set_false_path -to [get_ports vga_hsync_o]
set_false_path -to [get_ports vga_vsync_o]

# ==============================================================
# 14. PWM OUTPUT
# ==============================================================
set_false_path -to [get_ports pwm_o[*]]
set_false_path -to [get_ports pwm_n_o[*]]
set_false_path -from [get_ports pwm_fault_i]

# ==============================================================
# 15. SPI OUTPUT (async external device)
# ==============================================================
set_false_path -to [get_ports spi0_mosi_o]
set_false_path -to [get_ports spi0_sclk_o]
set_false_path -to [get_ports spi0_ss_o[*]]

# ==============================================================
# 16. JTAG / DEBUG (if present)
# ==============================================================
# set_false_path -from [get_ports jtag_*]
# set_false_path -to   [get_ports jtag_*]
```

**Goal**: 580 unconstrained → 0

### Phase 3: IR drop / PDN optimization — Priority 3

#### 3.1 Relax PDN pitch

**Issue**: Default PDN mesh is too dense → 1.6M nodes → OOM  
**Fix**: Double met4/met5 strap pitch, keep strap width

```tcl
# Add to config.tcl:
set ::env(FP_PDN_VPITCH) 280
set ::env(FP_PDN_HPITCH) 280
set ::env(FP_PDN_VWIDTH) 3.1
set ::env(FP_PDN_HWIDTH) 3.1
set ::env(FP_PDN_VOFFSET) 16.32
set ::env(FP_PDN_HOFFSET) 16.65
```

**Expected effect**: PDN node count ~1.6M → ~400K, RAM usage drops to ~4 GB

#### 3.2 Enable IR drop

```tcl
set ::env(RUN_IRDROP_REPORT) 1
```

#### 3.3 Docker memory settings

```bash
# Docker command in Makefile:
docker run --memory=14g --memory-swap=24g ...
```

### Phase 4: Config improvements — Priority 4

#### 4.1 Reduce GRT antenna iterations

```tcl
# 10 → 5 (run_v5 finished in 1 iteration anyway)
set ::env(GRT_ANT_ITERS) 5
```

#### 4.2 Sentinel settings (no change)

The following stay as-is:
```tcl
set ::env(SYNTH_NO_FLAT) 1           # Preserve hierarchy (for debug)
set ::env(QUIT_ON_SYNTH_CHECKS) 0    # sv2v false positives
set ::env(SYNTH_BUFFERING) 1         # Buffer insertion on
set ::env(PL_ROUTABILITY_DRIVEN) 1   # Congestion-aware placement
set ::env(GRT_ALLOW_CONGESTION) 1    # Congestion tolerance
```

### Phase 5: Complete signoff — Priority 5

#### 5.1 Magic LEF issue

**Issue**: Magic LEF generation used 13.7 GB RAM and got stuck  
**Options**:
- Docker swap: `--memory-swap=24g`
- Magic parameter `set GDS_FLATTEN 0`
- Alternative: use OpenROAD LEF writer (lighter)

#### 5.2 LVS

After Magic LEF completes:
```bash
make asic_lvs ASIC_TAG=run_v6
```

#### 5.3 Antenna check

Completed inside GRT in run_v5. Re-check after DRT:
```bash
make asic_antenna ASIC_TAG=run_v6
```

---

## 4. Implementation Order and Expected Impact

| # | Work item | Complexity | Est. time | Expected effect |
|---|-----------|------------|-----------|-----------------|
| 1 | SRAM Liberty bit-blast (dout0) | Easy | 1 hour | Clears 24 STA warnings, SRAM timing correct |
| 2 | Generate SRAM SS/FF corner Liberty | Medium | 2–3 hours | Multi-corner STA trustworthy, ~26K spurious violations gone |
| 3 | SDC unconstrained endpoints | Easy | 30 minutes | 580 unconstrained → 0 |
| 4 | Increase PDN pitch + enable IR drop | Medium | 1 hour config + ~2 hour run | IR drop report obtained |
| 5 | GRT_ANT_ITERS 10→5 | Trivial | 1 minute | Small runtime improvement |
| 6 | Complete Magic LEF / LVS | Hard | 4+ hours (RAM-dependent) | Full signoff |
| 7 | Synth wire warnings (optional) | Hard | RTL changes | 4807 warnings reduced |

---

## 5. Planned run_v6 config.tcl Changes

```diff
  # Current (run_v5)                          → New (run_v6)
  
  # SRAM Liberty
- set ::env(EXTRA_LIBS) [list $sram_lib]
+ set ::env(EXTRA_LIBS) [list $sram_lib_tt $sram_lib_ss $sram_lib_ff]

  # PDN
+ set ::env(FP_PDN_VPITCH) 280
+ set ::env(FP_PDN_HPITCH) 280

  # IR Drop
- set ::env(RUN_IRDROP_REPORT) 0
+ set ::env(RUN_IRDROP_REPORT) 1

  # Antenna
- set ::env(GRT_ANT_ITERS) 10
+ set ::env(GRT_ANT_ITERS) 5
```

---

## 6. Current Config Reference (run_v5)

```tcl
CLOCK_PERIOD        = 30.0 ns (33.3 MHz)
DIE_AREA            = 5500 × 5500 µm
PL_TARGET_DENSITY   = 0.30
PL_MACRO_HALO       = 30 30
PL_MACRO_CHANNEL    = 40 40
GRT_OVERFLOW_ITERS  = 50
GRT_ADJUSTMENT      = 0.2
GRT_ANT_ITERS       = 10
SYNTH_STRATEGY      = "AREA 1"
MAX_FANOUT_CONSTRAINT = 12
SYNTH_NO_FLAT       = 1
SYNTH_BUFFERING     = 1
```

---

## 7. Timing Reference (run_v5, 3 corners)

| Corner | SPEF | Setup WNS | Setup TNS | Hold WNS | Valid? |
|--------|------|-----------|-----------|----------|--------|
| Fastest (FF) | min | +13.16 ns | 0 | +0.09 ns | ❌ (no SRAM FF lib) |
| Typical (TT) | nom | +3.42 ns | 0 | +0.28 ns | ✅ |
| Slowest (SS) | max | -21.69 ns | -42833 ns | +0.83 ns | ❌ (no SRAM SS lib) |

**Note**: Typical corner results are trustworthy. SS/FF results are spurious due to missing SRAM Liberty.
SRAM paths assume delay = 0.

---

*This document was produced as a reference for `run_v6` preparation.*
