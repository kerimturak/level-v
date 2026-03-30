# Fixes history

Running log of **meaningful** RTL, simulation, and tooling changes: what we changed, why it was needed, and where to look in the tree. Entries are **newest first**.

Use this alongside one-off write-ups (e.g. [FIXES_APPLIED](FIXES_APPLIED.md) for the test-system batch) and reference docs such as [PERF_PIPELINE_LOG](PERF_PIPELINE_LOG.md).

---

## How to add an entry

Copy the block below, paste it **under the horizontal rule** at the top (below “## YYYY-MM-DD”), and fill in:

```markdown
### YYYY-MM-DD — Short title

| | |
|--|--|
| **Area** | hazard / memory / perf / sim / docs / build … |
| **Problem** | What was wrong or limiting? |
| **Change** | What we did (behaviour, not every line of diff). |
| **Rationale** | Why this approach; links to papers/issues if any. |
| **Files** | `path/one`, `path/two` |
| **Verify** | e.g. `make run_verilator TEST_CONFIG=isa TEST_NAME=rv32ui-p-lw` |
```

Keep each entry self-contained so a future reader does not need the chat log.

---

## 2026-03 — L2 miss-handling cycle counter (perf + pin)

| | |
|--|--|
| **Area** | L2, observability |
| **Problem** | `DMISS_STALL` / `IMISS_STALL` mix L1 back-pressure, store buffer, uncached, and L2 fill; no isolated L2 miss *service* cycle metric. |
| **Change** | `nbmbmp_l2_cache` drives `l2_miss_busy_o` in any cycle either I- or D-pipe is in miss service (MSHR alloc, victim WB, fill wait, or fill write to arrays). `perf_stall_counters` adds `cnt_l2_miss_cycles` (independent of `stall_cause`). `NO_L2_CACHE`: `cpu` ties `l2_miss_busy` low. |
| **Rationale** | Wall-clock cycles where L2 is doing real miss work; does not replace stall accounting and is not additive with `stall_cause` buckets. |
| **Files** | `rtl/core/mmu/nbmbmp_l2_cache.sv`, `rtl/core/cpu.sv`, `rtl/tracer/perf_stall_counters.sv` |
| **Verify** | `LOG_PERF_STALL=1` sim → `L2 miss cycles` line in log; hierarchy e.g. `…i_soc.i_l2_cache.l2_miss_busy_o` (wrapper names may differ). |

---

## 2026-03-30 — SSR-style load-use (hazard unit)

| | |
|--|--|
| **Area** | hazard, pipeline correctness / performance |
| **Problem** | Classic `lw_stall` stalled FE/DE and asserted `flush_ex_o` together with load-use detection. Flushing EX on that path removes the load from `pipe2` without replay, and stalls blocked the pipeline pattern where the consumer can enter EX in the same cycle the producer load enters MEM. |
| **Change** | Removed load-use FE/DE stall and load-use `flush_ex`. `flush_ex_o` is driven only by branch mispredict (`pc_sel_ex_i`). MEM→EX forwarding (`fwd_* = 2'b10`) plus `ex_mem_bypass_data` in `cpu.sv` supplies load/`ALU`/`PC+4` data from `pipe3` for operands. Dropped unused `hazard_unit` inputs (`rd_addr_ex_i`, `rslt_sel_ex_0`); updated `wave.do` and perf summary label (`ex-only` flush bucket). |
| **Rationale** | Aligns with the “forward from EX/MEM register” idea in SSR (arXiv:1912.10663): dependent in EX, producer load in MEM (`pipe3`), bypass from the MEM-stage register instead of an extra decode stall + EX bubble. |
| **Files** | `rtl/core/hazard_unit.sv`, `rtl/core/cpu.sv`, `wave.do`, `rtl/tracer/perf_stall_counters.sv` |
| **Verify** | ISA tests with load/use and branches, e.g. `rv32ui-p-lw`, `rv32ui-p-jalr`, `rv32ui-p-beq`; CoreMark + `LOG_PERF_STALL` — `LOAD_RAW_STALL` / load-use flushes should fall to ~0 for that class of hazard. |

---

## 2026-03 — MEM-stage bypass data for execution (`ex_mem_bypass_data`)

| | |
|--|--|
| **Area** | forwarding, execute stage |
| **Problem** | MEM→EX bypass mux used `pipe3.alu_result` for all `pipe3` forwards. For loads, the value to write back / forward is `read_data` (and similarly `pc_incr` for `JAL`), not the address in `alu_result`. |
| **Change** | Combinational `ex_mem_bypass_data` in `cpu.sv`: select by `pipe3.result_src` among `read_data`, `pc_incr`, `alu_result`; drive `execution.alu_result_i`. |
| **Rationale** | Correct forwarding when the consumer in EX needs the load result (or JAL link value) from the instruction currently in MEM. Complements SSR timing; does not by itself remove `LOAD_RAW` counters if decode stall was still present. |
| **Files** | `rtl/core/cpu.sv` |
| **Verify** | Load-use and JAL-heavy tests; compare against Spike where applicable. |

---

## 2026-03 — Pipeline performance logging (`LOG_PERF_STALL`)

| | |
|--|--|
| **Area** | observability, simulation |
| **Problem** | No structured visibility into stall causes, flush overlap, and active-cycle denominators for benchmarks. |
| **Change** | `perf_stall_counters.sv`: per–`stall_cause` buckets, flush-event buckets (trap / fence.i / BP / ex spill), overlap counters, `$display` summary at sim end. Makefile / Verilator / test runners pass `+define+LOG_PERF_STALL` or `LOG_PERF_STALL=1`; `verilator_runner.py` copies a snippet to `perf_pipeline.log`. |
| **Rationale** | Separate UART from perf; reproducible text artifact next to `verilator_run.log`. |
| **Files** | `rtl/tracer/perf_stall_counters.sv`, `rtl/flist.f`, `rtl/core/cpu.sv`, `rtl/include/level_defines.svh`, `makefile`, `script/python/makefile/verilator_runner.py`, `script/python/makefile/test_runner.py`, `script/config/tests/coremark.conf`, `script/python/debug_logger.py`, `docs/PERF_PIPELINE_LOG.md` |
| **Verify** | `make run_coremark` (or any run with `LOG_PERF_STALL=1`); inspect `results/logs/.../perf_pipeline.log` and sim `final` banner. |

---

*(Older entries can be appended here when you land new fixes.)*
