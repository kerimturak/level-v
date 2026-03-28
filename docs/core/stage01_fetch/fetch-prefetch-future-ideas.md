# Microarch ideas — fetch prefetch & memory subsystem

> **Status:** design notes only; not a commitment or specification.  
> **Scope:** started as **instruction fetch / prefetch** (`stage01_fetch`, `icache` interface); expanded here with **D-side** notes (store buffer, loads, **non-blocking D-cache** direction) as a single living scratchpad.

## Living document

This file is meant to **accumulate ideas over time**: new bullets, references, and measured outcomes can be appended as the team experiments. Keep entries **short and dated** if you add lab notes (e.g. “2026-03: next-line +1% on CoreMark in RTL sim — config X”).

---

## Current baseline

The core today combines:

- **`prefetcher_wrapper` / `next_line_prefetcher`:** After a demand miss completes on a **cacheable** line, requests **one** following cache line (line-aligned), serialized with the single low-level instruction port via `icache`’s prefetch handshake.
- **`icache`:** When `ENABLE_ICACHE_PREFETCH` is set, can accept a prefetch request when there is **no** demand miss, sharing fill logic with normal misses.
- **`align_buffer` + `fetch`:** Compressed ISA support, PC progression, and branch prediction interact with **when** sequential addresses are actually consumed.

This is **cache-line-oriented** prefetch, not (by default) a shallow 32-bit fetch FIFO in front of the bus.

---

## Reference core — [lowRISC Ibex `ibex_prefetch_buffer`](https://github.com/lowRISC/ibex/blob/master/rtl/ibex_prefetch_buffer.sv)

Ibex documents this block as a **prefetch buffer for a 32-bit memory interface**: it **caches instructions** in a small FIFO and, critically, supports **`NUM_REQS = 2`** outstanding instruction bus transactions with explicit **branch discard** of speculative data (`fifo_clear = branch_i`; comments note interaction with **FENCE.I**).

### Ideas transferable to Level-v (conceptual)

| Ibex mechanism | Possible Level-v analogue |
|----------------|---------------------------|
| 2-deep outstanding IF requests | Allow **more than one** I-side transaction in flight **if** the cache / Wishbone path can honor `gnt`/`rvalid` ordering without breaking single-port assumptions—or add a **thin IF queue** that legally overlaps handshakes. |
| Fetch FIFO + `fifo_ready` back-pressure | If the critical path is “IF waits one beat per `valid`”, a **small queue** between align logic and I$ could hide **fixed multi-cycle** RAM latency (orthogonal to **line** prefetch). |
| `branch_discard_*` on outstanding data | Any extra outstanding fetch must **track kill** on flush / mispredict / fence semantics so wrong-path instructions never reach decode—mirror Ibex’s discard flags in a minimal form. |
| Word-aligned address bump (`+4`) | Level-v is **RVC**-aware; a shallow queue must respect **16/32-bit** step width or attach **after** align resolution. |

### What Ibex does *not* replace

Ibex’s buffer is **not** a replacement for **next-cache-line** warmup: it mainly **pipelines narrow fetches** and cuts combinational depth to the I-side. Level-v’s **next-line** policy still matters for **miss-dominated sequential** code when fills are slow.

---

## Why measured IPC / benchmark gains can stay modest (expectations)

It is common to expect large gains from **instruction prefetch** and from **load/store or store buffers**, then see only a few percent (or noise) in simulation or on FPGA. Useful reasons to keep in mind:

### 1. The workload is often not memory-latency limited

CoreMark, Dhrystone, and many short tests already **mostly hit in L1** (or in fast SRAM models). **Hiding DRAM latency** only helps when the pipeline would otherwise **stall on miss**. If the limiter is **ALU chains, branches, or cache hits**, extra buffering adds little.

### 2. Amdahl /Instruction supply vs execution

Even a perfect I-side only speeds up the **fetch** slice of execution. If decode/execute or **mispredict recovery** dominates, I-side tweaks have a **low ceiling**.

### 3. Single port and serialization

If the I-cache (or unified backing port) allows **only one** outstanding fill or strictly serializes prefetch + demand, **next-line** still helps **only on the next miss**, not on **streams** of misses. **MSHR depth** and arbiter rules cap the benefit.

### 4. Branchy code and short traces

**Next-line** prefetch assumes **sequential** consumption soon. **Frequent branches**, OS / trap boundaries, or **ICMPI-heavy** control flow reduce **useful prefetch distance**.

### 5. Store / load buffers (D-side)

A **store buffer** mainly **decouples retirement from D-cache write timing** and can merge traffic; it does not turn a **compute-bound** kernel into memory-bound upside. Gains show up when **stores (or WAW ordering)** would stall the pipeline without the buffer, or when **non-blocking** behavior overlaps **late-fill** loads. If loads already hit or the buffer is shallow relative to latency, improvement is small—same **miss-rate / port** story as the I-side.

### 6. RTL sim vs silicon

Fast RAM models (or zero external contention) **understate** real memory delay, so prefetch and buffers **look less heroic** in sim; conversely, very fast L1 models **already** idealize the case where buffering helps least.

**Practical takeaway:** quantify **miss cycles**, **stall events**, and **MPC / IPC** before and after; attribute gains to **I-miss**, **D-miss**, **store stall**, or **branch** buckets. That avoids tuning the wrong knob.

---

## Direction 1 — Implement reserved `PREFETCH_TYPE` strategies

`level_param` and `prefetcher_wrapper` already reserve types **2–4** for richer policies. Concrete options:

1. **Stride / PC-delta prefetcher**  
   - Maintain a small **fully associative table** keyed by PC region or loop PC, learning `(PC, Δ)` where loads/stores or backward branches repeat.  
   - On a hit, prefetch `PC + k·Δ` for `k = 1 .. PREFETCH_DEGREE` (parameter already hinted in `level_param`).  
   - Best for **numeric kernels** and dense loops; must be **throttled** to avoid bus storms.

2. **Stream / sequential depth**  
   - Extend next-line to **degree N**: after confirming sequential consumption (PC advances by 2/4 bytes predictably), arm **multiple** line addresses subject to MSHR / port limits.  
   - Requires clear rules when **taken branches** or **exceptions** flush training state.

3. **Hybrid**  
   - Next-line as default; escalate to stride when the same PC band triggers repeated next-line hits (optional confidence counter).

**Interface needs:** today the prefetch FSM sees `miss_addr_i` and miss status. Stride/stream may need **observed PC** and **retire or fetch-valid hints** from `fetch` (or a narrow side channel) without bloating the critical path—likely **registered** observation samples.

---

## Direction 2 — I-cache / memory subsystem coupling

Prefetch usefulness is bounded by **how many fills** can be in flight and how **replacement** interacts with pollution.

- **Multiple outstanding misses (MSHR depth):** If the memory side evolves to support **more than one** I-side fill, prefetch degree can be raised without serializing every line.  
- **Prefetch-only hint to L2:** Mark prefetch fills as **lower priority** than demand if an arbiter or L2 queue exists, so latency-sensitive demand wins under load.  
- **Victim / way prediction:** Aggressive prefetch can increase **conflict misses**; tie-in with **PLRU / eviction policy** (or a small prefetch filter “do not prefetch if set is thrashing”) is worth measuring in simulation.

---

## Direction 3 — Alignment with control flow

- **Branch predictor integration:** On **high-confidence predicted taken** branches, optional **target-line** prefetch (one line at target) may help **I$ cold** paths; must respect **PMA** (uncached regions) and not fight **FENCE.I** semantics.  
- **RVC (compressed) streams:** Sequential PC steps are 2 or 4 bytes; a future prefetcher could use **effective fetch width** from the align buffer to avoid over-fetch assumptions.

---

## Direction 4 — Shallow fetch queue (Ibex-style, same as “thin front-end”)

If profiling shows **bubbles** not explained by misses (e.g. strict single-beat gating on the path to I$), a **small FIFO + limited outstanding** requests—along the lines of [Ibex’s prefetch buffer](https://github.com/lowRISC/ibex/blob/master/rtl/ibex_prefetch_buffer.sv)—may help **only if** the **Wishbone / L2** contract allows **overlapping** or pipelined transactions safely.

This is a **larger** microarch change than extending `next_line_prefetcher`; validate with cycle-accurate traces and **flush / discard** rules consistent with compressed fetch and fences.

---

## Direction 5 — Store / load path and **non-blocking D-cache** (future)

Today’s baseline (see [Memory](../stage04_memory/memory_module.md), [Store buffer](../stage04_memory/store_buffer_module.md)) is **in-order** at the MEM stage, with a **FIFO store buffer** (drain oldest to D$, **store→load forwarding** and **conflict** handling on the same word) and **no separate load queue**—pending loads are a small bit of FSM, not an OoO-style LDQ.

### Store buffer — possible evolutions

- **Deeper / parameterized depth** (`SB_DEPTH`) tuned after profiling real workloads (not only CoreMark).  
- **Coalescing / merging** of adjacent or same-line stores before drain (reduces D$ traffic if policy stays correct for RV weak ordering and fences).  
- Clearer **FENCE / FENCE.I** interaction documentation + tests if SB + D$ ordering is extended.  
- If D$ becomes **non-blocking**, SB drain may need **retry / back-pressure** semantics and arbitration with **in-flight load misses** (see below).

### Load path — possible evolutions

- A minimal **load miss buffer** (MSHR-lite): track **one or few** outstanding D$ read misses so the pipeline or **later independent ops** (where hazards allow) are not serialized as aggressively as today—*only if* the rest of the core can exploit it without breaking in-order semantics.  
- **Explicit load queue** is usually coupled with **wider issue or non-blocking D$**; treat as a stepping stone, not a standalone knob.

### Non-blocking D-cache (longer-term)

The **L2** path already explores **non-blocking, multi-bank** behavior (`nbmbmp_l2_cache`, see [L2 cache](../mmu/l2_cache_module.md)). A natural stretch goal is a **non-blocking L1 D-cache**:

- **Multiple outstanding misses** (small MSHR table): overlap **fill latency** with **independent** instructions (limited by in-order issue, but still useful for **late-hit** or **critical-word-first** style fills).  
- **Load hits** while **one miss** is outstanding (classic “hit under miss” subset): requires **banking / tag–data separation** and careful **store-buffer** ordering vs. returning fill data.  
- **Prefetch integration:** D-side hardware prefetch (stride/stream) pays off most when misses can overlap; non-blocking D$ raises the **ceiling** for those policies.

**Risk / cost:** verification cost jumps (memory ordering, SB forwarding vs. fill race, FENCE). Prefer **parameterized** `NONBLOCKING_DDEPTH` or similar and grow tests incrementally.

### Relation to high-end cores (sanity check)

OoO cores (e.g. [XiangShan](https://github.com/OpenXiangShan/XiangShan) class) combine **deep store queues + load queues + non-blocking caches** with **out-of-order scheduling**; Level-v gains remain **bounded by sequential issue** until the front-end / issue model changes. Non-blocking D$ still helps **miss latency hiding** even in-order.

### Appendix — Reference repos: store vs load buffering & forwarding (notes)

> **Purpose:** when Level-v adds a **distinct load buffer / queue** (beyond today’s `load_pending`) and evolves **store–load forwarding**, these projects are starting points for RTL or architecture mining.  
> **Caveat:** rows are **README / high-level** unless you open the RTL; module names and queue depths change with branches—**re-validate before citing in a paper or porting code**.

| Project | Store-side structure | Load-side structure | Forwarding / disambiguation (high level) | Relevance to Level-v |
|---------|----------------------|---------------------|------------------------------------------|----------------------|
| **Level-v** (this tree) | [`store_buffer.sv`](../stage04_memory/store_buffer_module.md): FIFO, drain to D$, byte-wise merge | No LDQ; [`memory.sv`](../stage04_memory/memory_module.md) `load_pending` + D$ arb | SB→load **combinational** merge; `fwd_conflict` → stall / drain | **Baseline** to extend |
| [ApogeoRV](https://github.com/GabbedT/ApogeoRV) | README: **store buffer** | OoO core: likely **load queue / LSQ** inside LSU (not spelled “LB” on README) | README: **load forwarding** from store path; OoO **ordering** | **MIT** SV; study `Hardware/` for STQ/LDQ split & replay |
| [XiangShan](https://github.com/OpenXiangShan/XiangShan) | Deep **store queue** (Chisel LSU) | **Load queue** + miss handling | Full **LSQ** disambiguation, **non-blocking** memory | Best **architecture** reference for split SB/LB (scale is huge) |
| [riscv-boom](https://github.com/riscv-boom/riscv-boom) | **STQ** | **LAQ** / load miss track | Documented **LSQ**; replays, youngest-store rules | Academic OoO; clearer **block diagram → RTL** trail than some industrial repos |
| [Ibex](https://github.com/lowRISC/ibex) | LSU-integrated (**no** big split SB/LB like OoO) | Same LSU path | **Stall / single outstanding** style; see `ibex_load_store_unit` | **In-order** reference; **not** where to copy LDQ from |
| [AngeloJacobo/RISC-V](https://github.com/AngeloJacobo/RISC-V) | No real store buffer | No load buffer | [`rv32i_forwarding.v`](https://github.com/AngeloJacobo/RISC-V) = **register** forwarding only | Teaching core; **not** LS-buffer reference |
| [quasiSoC](https://github.com/regymm/quasiSoC) CPU | Simple multi-cycle store path                     | Simple load path         | Software / timing model differs from pipelined LSQ                                                    | **SoC/Linux**, not LS microarch |
| [phoeniX](https://github.com/phoeniX-Digital-Design/phoeniX) | **No** store buffer; store in **MW** comb. to bus | **No** LDQ; load in **same MW** stage | **Register** fwd only (EX/MW→DE); **load-use = stall**; subword via `frame_mask` on **word** bus | Contrast to Level-v SB; see detail below |

#### phoeniX — load/store / stall / forward (RTL summary, `main`)

Source: top [`phoeniX.v`](https://github.com/phoeniX-Digital-Design/phoeniX/blob/main/phoeniX.v), [`Load_Store_Unit.v`](https://github.com/phoeniX-Digital-Design/phoeniX/blob/main/Modules/Load_Store_Unit.v), [`Hazard_Forward_Unit.v`](https://github.com/phoeniX-Digital-Design/phoeniX/blob/main/Modules/Hazard_Forward_Unit.v). **GPL-3.0.**

1. **Stores — not “merged” in a buffer**  
   - Store data is registered as `rs2_MW_reg` in the combined **Memory/Writeback** stage; `Load_Store_Unit` drives a **32-bit word-aligned** address and a **4-bit `frame_mask`** (byte lane enables).  
   - Subword stores place `store_data` in the selected lane(s) and drive **`z`** on unused lanes on the bidirectional `memory_interface_data` (classic masked write pattern). There is **no** FIFO of pending stores and **no** store-to-load forwarding path in hardware.

2. **Loads — not merged across transactions**  
   - Load uses the same unit: one memory read presents a full word; **extract / sign-extend** of byte/halfword is **purely combinational** from `memory_interface_data` and `funct3` / `frame_mask`.  
   - **Unaligned** access is **not** supported in LSU (README); Level-v + specs are stricter/softer per implementation.

3. **Register forwarding (not LSQ)**  
   - `Hazard_Forward_Unit`: two **writeback sources** compared to `rs1`/`rs2` in decode — **`write_index_EX_reg` + `execution_result_EX_wire`** (with special cases for LUI/AUIPC/SYSTEM) and **`write_index_MW_reg` + `write_data_MW_wire`** (includes **ALU/MUL/DIV/JAL/LUI/LOAD/CSR** result after MW).  
   - So ALU results can bypass from EX or MW; **load result only exists in `write_data_MW_wire` after the load completes in MW**.

4. **Stalls**  
   - `stall_condition[1]`: **MUL/DIV busy** (`mul_busy_EX_wire || div_busy_EX_wire`).  
   - `stall_condition[2]`: **load–use hazard** — `opcode_EX_reg == LOAD` and EX writes a register that **decode still needs** as `rs1` or `rs2` (`read_enable` gating). Pipeline inserts bubbles (PC/decode freeze; EX can be cleared on this stall per the DE→EX `always` sensitivity). **No** bypass from a load still in EX.

5. **`Register_Loading_Table`**  
   - Side table logging **load target address** when a load completes (`write_enable_MW_reg && opcode_MW_reg == LOAD`); **not** used in the forwarding/storedatapath in the snippet above—approximate / profiling hook per project docs.

**Takeaway for Level-v:** phoeniX is a **minimal in-order** reference: **simpler** than your **store buffer + youngest-byte merge**. Use it to contrast **“bare LSU + load stall”** vs your **“SB drain + SB→load forward + conflict stall”** when documenting design trade-offs.

**Level-v direction (reminder):** splitting **load buffer** from “pending bit” usually implies: (1) tracking **multiple** in-flight loads if D$ allows, (2) explicit **RAW** resolution vs SB **youngest-first** byte merge, (3) **FENCE** / flush interaction with both structures—align tests with [memory model docs](../../fence-i-implementation.md) (and related notes) / ordering goals.

---

## Direction 6 — RTOS & peripheral bring-up (software / SoC goals)

Hardware microarch is only part of the story; **product-style** goals include **FreeRTOS-class RTOS**, a **thin BSP** over UART/GPIO/CLINT/PLIC, and scripted build+sim like reference teaching cores.

- **Reference:** [AngeloJacobo/RISC-V](https://github.com/AngeloJacobo/RISC-V) — RV32I+Zicsr Verilog, **FreeRTOS**, `test/` regression, peripheral C library. Use for **workflows and SDK layout**, not as an RTL substitute (different ISA subset, Harvard vs Wishbone).  
- **Where tracked in-tree:** [SoC roadmap](../../soc-roadmap.md) — section *Software, peripherals, and RTOS (community reference)*.  

---

## Validation and metrics

Any new policy should be gated behind parameters and evaluated with:

- **CoreMark / Embench** (realistic I-footprint),
- **RISC-V DV** or long random ISA runs (stress predictor + flush),
- **Hit/miss/prefetch-fill counters** exported (if not already) to quantify pollution vs. coverage,
- Optional: **synthetic I-miss heavy** microbenchmarks (large cold loops) to stress prefetch *unlike* tiny compliance tests.

---

## References (in-tree)

- External LSQ-oriented open cores (to mine with caution): [ApogeoRV](https://github.com/GabbedT/ApogeoRV), [XiangShan](https://github.com/OpenXiangShan/XiangShan), [riscv-boom](https://github.com/riscv-boom/riscv-boom), in-order counter-example [Ibex LSU area](https://github.com/lowRISC/ibex/tree/master/rtl); minimal LSU + load-stall reference [phoeniX](https://github.com/phoeniX-Digital-Design/phoeniX)  
- [Fetch module](fetch_module.md)  
- [Align buffer](align_buffer_module.md)  
- [Next-line prefetcher](next_line_prefetcher_module.md)  
- [Prefetcher wrapper](prefetcher_wrapper_module.md)  
- [I-cache](../mmu/icache_module.md)  
- Memory stage / store path (D-side buffering context): [Memory module](../stage04_memory/memory_module.md), [Store buffer](../stage04_memory/store_buffer_module.md)  
- [D-cache](../mmu/dcache_module.md), [L2 cache](../mmu/l2_cache_module.md) (non-blocking direction)  
