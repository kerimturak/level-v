CoreMark env/common build helper
================================

This helper builds CoreMark using the `env/common` startup files provided in this repository. It produces an ELF, a raw binary, and (if available) a `.mem` file suitable for simulator memory initialization.

Usage
-----

From the repo root run:

```
./tools/build_coremark_env.sh [--coremark-dir DIR] [--cross PREFIX] [--out-dir DIR] [--iterations N]
```

Defaults:
- `COREMARK_DIR`: `../coremark` (relative to repo root)
- `CROSS`: `riscv32-unknown-elf-`
- `OUT_DIR`: `build/tests/coremark_env`
- `ITERATIONS`: `1`

Example:

```
./tools/build_coremark_env.sh --coremark-dir /home/kerim/coremark --iterations 1
```

What the script does
--------------------
- Compiles CoreMark sources plus `env/common/crt.S` and `env/common/syscalls.c`.
- Uses linker script `env/common/test.ld` to place sections at 0x8000xxxx VMAs.
- Attempts to compile with `-march=rv32imc_zicsr` first (for CSR instructions), falls back to `rv32imc`.
- Produces `coremark.elf`, `coremark.bin` and (if `tools/elf_to_mem.py` exists) `coremark.mem` in the output directory.

Running on Spike
----------------
If you want to run on spike directly (no `pk`), use a command like:

```
spike --isa=rv32imc -m0x80000000:64M build/tests/coremark_env/coremark.elf
```

If your simulator needs a `.mem` file, use the produced `coremark.mem` (copy it to the simulator's expected path or pass as an init file).

Notes & troubleshooting
-----------------------
- If the assembler complains about CSR instructions, ensure your RISC-V toolchain supports the required extensions; the script attempts `rv32imc_zicsr` first.
- If `core_portme.h` or `encoding.h` cannot be found, pass `--coremark-dir` pointing to a CoreMark checkout that contains `core_portme` in `barebones` or `posix` ports.
- The script requires a riscv toolchain (`riscv32-unknown-elf-gcc` / `objcopy`) in `PATH` by default; override with `--cross` if you use a different prefix.

Contact
-------
If build fails, paste the compiler output and I can help adjust the include paths or flags.
