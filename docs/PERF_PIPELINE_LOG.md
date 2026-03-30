# Pipeline performance log (`LOG_PERF_STALL`)

This document explains the RTL pipeline accounting enabled by `**+define+LOG_PERF_STALL**` (see `rtl/tracer/perf_stall_counters.sv`, instantiated from `rtl/core/cpu.sv`). It is meant to help interpret `**results/logs/verilator/<test>/perf_pipeline.log**` (and the same block at the end of `**verilator_run.log**`).

---

## Enabling and outputs

- **Build:** `make verilate TEST_CONFIG=coremark` (CoreMark profile sets `LOG_PERF_STALL=1` in `script/config/tests/coremark.conf`), or pass `LOG_PERF_STALL=1` when verilating.
- **Run:** `make run_coremark SIM_FAST=1` (or your usual Verilator flow).
- **Artifacts:**
  - `results/logs/verilator/<test>/perf_pipeline.log` — extracted summary (when the Python runner sees the `LOG_PERF_STALL` banner in simulator output).
  - Full simulator stdout/stderr: `verilator_run.log`.

**Counters reset** when CPU `rst_ni` is low, except `**cycles_clk_total**`, which counts every clock edge for the whole simulation (including reset).

**Denominator for percentages:** `**cycles_active**` = cycles with `rst_ni == 1` (the “benchmark window” in typical bring-up runs). Your workload may include reset/release and shutdown; interpret percentages accordingly.

---

## Stall causes (cycles)

A **stall cycle** is any cycle where `stall_cause != NO_STALL` in `cpu.sv`. Only **one** stall reason is recorded per cycle (priority below).

### Priority order (hardware)

Highest to lowest:

1. `FENCEI_STALL` — FENCE.I / related D-cache writeback stall
2. `IMISS_STALL` — I-cache miss
3. `DMISS_STALL` — D-cache / memory miss
4. `LOAD_RAW_STALL` — load-use hazard (`fe_stall || de_stall` from `hazard_unit`)
5. `ALU_STALL` — multi-cycle multiply/divide

If a lower-priority condition could also be true in the same cycle, the counter only attributes the **winning** cause.

---

### `LOAD_RAW_STALL`


|                       |                                                                                                                                                                                                                                                                                         |
| --------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Meaning**           | `lw` is in **EX** while decode still needs its `rd` (`lw_stall` in `hazard_unit.sv`). One FE/DE stall cycle is normal; then the consumer enters EX while the load is in **MEM**.                                                                                                                                      |
| **Typical sources**   | `lw` immediately followed by an op that uses the loaded register.                                                                                                                                                                                                                      |
| **Hardware**          | MEM→EX bypass must use **`pipe3.read_data`** for loads (and **`pc_incr`** for JAL), not `pipe3.alu_result` (effective address for loads). Implemented as `ex_mem_bypass_data` feeding `execution.alu_result_i` in `cpu.sv`.                                                                                   |
| **Improvement ideas** | Schedule an **independent** instruction in the slot after `lw`; deeper cores (dual-issue, OoO) hide latency.                                                                                                                                                                            |


---

### `IMISS_STALL`


|                       |                                                                                                                                                                                                                                                                     |
| --------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Meaning**           | Instruction fetch blocked on **I-cache / refill** (front-end not delivering an instruction on time).                                                                                                                                                                |
| **Typical sources**   | Working-set larger than I-cache, conflict misses, cold start, interaction with L2/backing memory latency.                                                                                                                                                           |
| **Improvement ideas** | Larger or more associative **I-cache**; **line size / prefetch** (next-line or stream buffer); reduce **code footprint** (`-Os`, hot/cold splitting); align critical loops to reduce tag pressure; tune **branch-fetch** so fewer wrong-path fills pollute I-cache. |


---

### `DMISS_STALL`


|                       |                                                                                                                                                                                                                                                                                                                          |
| --------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| **Meaning**           | Pipeline stalled on **D-cache miss** or downstream memory latency (unified path through memory subsystem as wired in `cpu.sv`).                                                                                                                                                                                          |
| **Typical sources**   | Data working set vs D-cache capacity; capacity/conflict misses; long L2/AXI latency in simulation or silicon.                                                                                                                                                                                                            |
| **Improvement ideas** | Larger **D-cache** or higher sets/ways; **write policy** / **write buffer** tuning; **L2 size and latency**; **critical word first** / **early restart** if supported; software **data layout** (structure packing, blocking) to improve locality. Often the **largest stall bucket** on embedded kernels like CoreMark. |


---

### `ALU_STALL`


|                       |                                                                                                                                                                                                         |
| --------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Meaning**           | Execute held on **multi-cycle M-extension** operations (multiply/divide implementation as configured in RTL).                                                                                           |
| **Typical sources**   | Hot loops with `mul`/`div`/`rem`; soft divisions from runtime/helper code.                                                                                                                              |
| **Improvement ideas** | Faster **divider** (radix, pipelining) if area/timing allow; **fused patterns** where ISA permits; **compiler** strength reduction (shifts for powers of two); avoid divide in inner loops if possible. |


---

### `FENCEI_STALL`


|                       |                                                                                                                              |
| --------------------- | ---------------------------------------------------------------------------------------------------------------------------- |
| **Meaning**           | Stall while **FENCE.I** semantics complete (including D-cache dirty writeback / coherence with I-stream as implemented).     |
| **Typical sources**   | Self-modifying code, JIT barriers, explicit `fence.i` in firmware.                                                           |
| **Improvement ideas** | Rare in benchmarks; if non-zero, ensure **minimal fence.i** in runtime; faster **writeback path** so fence completes sooner. |


---

## Flush events (counted once per cycle)

A **flush event** is recorded in at most **one** category per cycle, using this **priority**:

1. **EX trap** — `priority_flush == 3` (exception taken in execute).
2. **DE trap** — `priority_flush == 2` (decode/front-side exception path).
3. **FENCE.I / MISA front flush** — `fencei_flush` (I-cache / decode flush for `fence.i` or `misa` write affecting decode, as in `cpu.sv`).
4. **BP miss redirect** — `de_flush_en` effective: branch predictor **wrong** (`hazard_unit` `pc_sel_ex_i` is wired to `**!ex_spec_hit**` in `cpu.sv`, not raw “branch taken”).
5. **Load-use EX only** — `ex_flush_en && !de_flush_en`: **load-use** inserts an EX-stage bubble without a decode-stage redirect from misprediction.

`flush_de_o` / `flush_ex_o` are **masked** when `stall_cause` is one of `IMISS_STALL`, `DMISS_STALL`, `ALU_STALL`, or `FENCEI_STALL`; counting uses the **masked** `de_flush_en` / `ex_flush_en` signals.

---

### EX trap / DE trap


|                       |                                                                                                                       |
| --------------------- | --------------------------------------------------------------------------------------------------------------------- |
| **Meaning**           | Trap to M-mode:** EX**-stage fault wins over DE/FE in priority encoding.                                              |
| **Improvement ideas** | Should be **near zero** on validated benchmarks; nonzero → debug **PMA**, alignment, illegal opcode, interrupt storm. |


---

### FENCE.I / MISA front flush


|                       |                                                                                                     |
| --------------------- | --------------------------------------------------------------------------------------------------- |
| **Meaning**           | Front-end invalidated for **instruction stream coherence** or **compressed ISA** change (`misa.C`). |
| **Improvement ideas** | Minimize `**fence.i**` in steady-state code; avoid toggling `**misa**` in performance paths.        |


---

### BP miss redirect


|                       |                                                                                                                                                                                                                                        |
| --------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Meaning**           | **Speculation wrong**: resolved PC disagrees with predicted path (`!ex_spec_hit`).                                                                                                                                                     |
| **Typical sources**   | Hard branches, BTB/RAS misses, PHT aliasing, short history.                                                                                                                                                                            |
| **Improvement ideas** | Deeper **GHR**, larger **BTB/RAS**, **tagged** or **partial** predictors; **loop predictor** for inner loops; **better return address stack** pairing with call/ret; **compiler** branch layout to reduce pressure on same index bits. |


---

### Load-use EX only


|                  |                                                                                                                                                                                                                                   |
| ---------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Meaning**      | `**flush_ex_o**` from load-use (`lw_stall                                                                                                                                                                                         |
| **Overlap note** | Often correlates with `**LOAD_RAW_STALL`**; `**cycles_stall_with_flush**` counts cycles where **both** a stall and a counted flush occurred. **Do not add** stall % and heuristic flush bubble % and treat as independent losses. |


---

## Reading the summary lines

- **Stall cycles (% of active):** fraction of post-reset cycles spent **not** advancing the front-end for the dominant stall reason above.  
- **Cycles w/o stall:** complement of stall cycles (same denominator).  
- **Flush events (% of cycles with ≥1 flush):** at most **one event per cycle**, so this is “what fraction of cycles squashed the pipe for a counted flush reason.”  
- **Flush ×2–×3 heuristic:** rough **bubble cost** if each flush costs 2–3 fetch/decode slots — **overlaps** with cycles that are also stalled; use as intuition, not as an additive IPC formula.

---

## Related RTL / docs


| Item                      | Location                                            |
| ------------------------- | --------------------------------------------------- |
| Stall enum & pipeline doc | `rtl/pkg/level_param.sv`, `docs/core/cpu_module.md` |
| Hazard / flush sources    | `rtl/core/hazard_unit.sv`, `rtl/core/cpu.sv`        |
| Feature define            | `rtl/include/level_defines.svh` (`LOG_PERF_STALL`)  |
| CoreMark profile          | `script/config/tests/coremark.conf`                 |


---

## Limitations

- Counts reflect **this core’s** stall/flush encoding; they are not a substitute for **cycle-accurate** power or bus tracing.  
- **EEMBC CoreMark** “valid run” rules (e.g. minimum time) are **orthogonal**; you can still use this log to profile the pipeline on short or validation runs.  
- RTL simulation **includes memory model latency**; **DMISS** dominance may differ on FPGA vs ASIC vs fast RAM models.

