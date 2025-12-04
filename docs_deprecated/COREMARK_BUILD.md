CoreMark build & configuration for Ceres core

Overview
--------
This document explains how CoreMark is configured and built for the Ceres RISC‑V core in this repository, which files I changed to port CoreMark to the barebones target, and the exact commands used to produce the artifacts (`.elf`, `.bin`, `.mem`, and `.dump`). It also explains how to change UART/timer configuration and how to run the simulator with the generated images.

Files changed / important locations
----------------------------------
- subrepo/coremark/barebones/core_portme.h
  - Enabled `HAS_STDIO` / `HAS_PRINTF`, defined fallback `FLAGS_STR`, and included required headers.
- subrepo/coremark/barebones/core_portme.c
  - Implemented `barebones_clock()` using the RISC‑V cycle CSR (rdcycle), implemented `ee_printf()` to send output to the memory-mapped UART, added `init_uart()` and call it from `portable_init()` to initialize the UART early.
- tools/setup_coremark.sh
  - Helper script to copy CoreMark sources, compile with either the cross toolchain or host `gcc` fallback, produce `coremark.elf`, `coremark.bin`, and create `build/tests/mem/coremark.mem` using `tools/elf_to_mem.py`.
- build/tests/coremark/
  - Output artifacts are copied here: `coremark.elf`, `coremark.bin`, `coremark.mem`, `coremark.dump`, `coremark_words_le.dump`.

How CoreMark is configured for this core
---------------------------------------
1. Toolchain
   - Default CROSS prefix: `riscv32-unknown-elf-` (changeable via `--cross` argument to the helper script).
   - If the cross compiler is not available the script falls back to host `gcc` for quick iteration but that binary will be a host ELF (not runnable on target).

2. Build flags
   - For cross builds: `-march=${MARCH} -mabi=${MABI} -O2 -static -nostdlib -ffreestanding -fno-builtin -DCOREMARK_PORTME_USE_STDINT -DVALIDATION_RUN`
   - For host fallback: `-O2 -DCOREMARK_PORTME_USE_STDINT -DVALIDATION_RUN`
   - `VALIDATION_RUN` is defined so CoreMark's seed/timing code is included.

3. Linker
   - For cross builds the script uses `-Ttext=0x80000000` and links statically. The ELF entry default is allowed to be the default `_start` provided by the C runtime or by the link script; this simple build uses `-Ttext` and relies on the startup provided by the barebones port.

4. UART and Timer mapping used in the port
   - UART registers used in `core_portme.c` (matches your `tekno.h` example):
     - `UART_CTRL` = 0x20000000
     - `UART_STATUS` = 0x20000004 (tx_full is bit 0)
     - `UART_WDATA` = 0x2000000c
   - CPU clock constant used: `CPU_CLK = 50000000` and `BAUD_RATE = 115200` (baud divisor computed as `CPU_CLK/BAUD_RATE`).
   - Timer read is done via `rdcycle()` for RISC‑V; `barebones_clock()` returns the lower 32 bits of `rdcycle` on RV32.

Creating the artifacts (commands used)
-------------------------------------
From the repository root run:

1) Build CoreMark and generate `.elf`, `.bin`, `.mem`:

```bash
./tools/setup_coremark.sh --coremark-dir subrepo/coremark
```

Optional arguments:
- `--cross <prefix>` e.g. `--cross riscv64-unknown-elf-` to use a different toolchain prefix
- `--march <isa>` e.g. `--march rv32imc` (default used by script)
- `--mabi <mabi>` e.g. `--mabi ilp32`

Outputs placed by the helper script:
- `build/coremark_build/coremark.bin` (binary)
- `build/coremark_build/coremark_src/coremark.elf` (ELF in the copied tree)
- `build/tests/mem/coremark.mem` (.mem formatted for $readmemh via `tools/elf_to_mem.py`)

2) Additional dumps (created by the helper actions)
- `build/tests/coremark/coremark.dump` — one hex byte per line (useful for byte-oriented tools)
- `build/tests/coremark/coremark_words_le.dump` — 32-bit little-endian words, one hex word per line, in `0x12345678` format (useful for memory load formats expecting 32-bit words)

How to use the `.mem` with your simulator
-----------------------------------------
When running Verilator or ModelSim, pass the INIT_FILE plusarg used by the testbench, for example with the previously used test harness:

Verilator run example:

```bash
build/obj_dir/Vceres_wrapper 200000 \
  +INIT_FILE=$(pwd)/build/tests/coremark/coremark.mem \
  +simulator=verilator +test_name=coremark \
  +fetch_log=results/logs/verilator/coremark/fetch_trace.log \
  +log_path=results/logs/verilator/coremark/ceres.log \
  +DUMP_FILE=results/logs/verilator/coremark/waveform.fst
```

ModelSim/Questa (batch) example:

```bash
vsim -c build/work.tb_wrapper -do "run 200000ns; quit" -t ns \
  +define+FETCH_LOGGER +fetch_log=results/logs/modelsim/coremark/fetch_trace.log \
  +INIT_FILE=$(pwd)/build/tests/coremark/coremark.mem \
  +addr_file=$(pwd)/build/tests/coremark/pass_addr.txt
```

Where to change UART/timer settings
----------------------------------
- Edit `subrepo/coremark/barebones/core_portme.c` to change the UART register addresses/bit fields if your core's UART is at different addresses.
- Change `CPU_CLK`/`BAUD_RATE` in the same file (or provide these via a header like `tekno.h`) to match your platform.
- `barebones_clock()` currently reads `rdcycle`; if your platform exposes a different timer peripheral, replace that implementation with reads from your timer registers.

Reproducible steps (minimal)
----------------------------
1. Ensure `subrepo/coremark` exists (script clones it if missing).
2. Run the setup script:

```bash
./tools/setup_coremark.sh --coremark-dir subrepo/coremark
```

3. Use `build/tests/coremark/coremark.mem` as `+INIT_FILE` for simulation.

If you want a different memory format
-----------------------------------
- `tools/elf_to_mem.py` accepts block size, word-size, endianness and word-order options; use it to generate other formats.
- If you need Intel HEX or S-record, I can add a converter or extend `elf_to_mem.py`.

Support and next steps
----------------------
- I created `build/tests/coremark/coremark.dump` (byte-per-line) and `build/tests/coremark/coremark_words_le.dump` (32-bit little-endian words) as requested.
- If you want those in another format (Intel HEX, SREC, 8/16/32-bit words with different endianness), tell me the exact format and I'll add a converter and regenerate.
- I can also update `tools/setup_coremark.sh` to accept an explicit `--dump-format` flag and generate all formats automatically.

Contact
-------
If you give me the exact `.dump` format your simulation flow expects (e.g. 32-bit hex words for `$readmemh`, Intel HEX, or a simple raw hexdump), I will regenerate and place it in `build/tests/coremark/` and update the docs accordingly.
