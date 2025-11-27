CoreMark helper

This folder includes `setup_coremark.sh` which will:

- Initialize git submodules (if present)
- Clone the CoreMark repository into `coremark/` if missing
- Create a small out/ directory and compile CoreMark with your CROSS toolchain
- Produce ELF, binary, and a `.mem` file using `tools/elf_to_mem.py`

Usage examples:

```bash
# use defaults (CROSS=riscv32-unknown-elf-, MARCH=rv32imc)
./tools/setup_coremark.sh

# customize toolchain, ISA and output path:
CROSS=riscv64-unknown-elf- MARCH=rv32imc MABI=ilp32 ./tools/setup_coremark.sh --coremark-dir coremark
```

If compilation fails, adjust `CROSS`, `MARCH` and `MABI` environment variables to match your RISC-V toolchain.
