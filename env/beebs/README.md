# BEEBS (upstream) + Level-V

[BEEBS](https://github.com/mageec/beebs) is the Bristol Embedded Energy Benchmark Suite. It uses **Autoconf** and per-target **`--with-chip` / `--with-board`** board ports under `config/`. There is **no** stock Level-V chip/board entry today.

## Submodule + native build (this repo)

```bash
make beebs_clone    # git submodule update --init --depth 1 subrepo/beebs
make beebs_build    # ./configure && make — **host** (e.g. x86_64) binaries under subrepo/beebs/src/*/
make beebs_distclean
```

`subrepo/beebs` is a **git submodule** (GPL-3.0 — review before redistribution).

**Nereye build oluyor?** `make beebs_build` → `subrepo/beebs` içinde `./configure && make`. Çıktılar **host** ikilileri: her benchmark için `subrepo/beebs/src/<isim>/` altında çalıştırılabilir (ör. `crc32`, `aha-mont64`). **Level-V `.mem` üretilmez** — o, RV32 chip/board portu + `objcopy`/ELF→MEM akışı gerektirir (şimdilik `make embench` / `make custom_build` kullan).

## Full port (manual)

1. Add `config/chip/level-v/` and `config/board/levelwrapper/` (or similar) following an existing small ARM/RISC-V example if present in the tree you clone.
2. Implement `boardsupport.c`: `initialize_board`, `start_trigger`, `stop_trigger` (GPIO toggles and/or **UART** if you want FPGA-visible output).
3. Configure with your `riscv32-unknown-elf` triple and the new chip/board names.
4. Produce `.mem` images with the same flow as Embench (`elf_to_mem.py`, load at `0x80000000`).

Until that port exists, use **Embench-IoT** (`make embench`) and the **custom** demos in `sim/test/custom/` (e.g. `dsp_fir_mac_test`, `crc32_demo_test`) for RISC-V + UART on Level-V.
