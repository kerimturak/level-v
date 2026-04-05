# TensorFlow Lite Micro — Level-V (scaffold)

Upstream: [github.com/tensorflow/tflite-micro](https://github.com/tensorflow/tflite-micro) → `subrepo/tflite-micro`.

## Porting outline

1. **Generate** or copy a `riscv32` / `rv32imac` embedded target under  
   `tensorflow/lite/micro/tools/make/targets/` and a matching **compiler flags** file (see existing `bluepill`, `sparkfun` examples).
2. **Syscall / libc**: match newlib-nano + `env/common` patterns used by CoreMark (`crt0`, UART printf).
3. **Memory**: use `env/tflite-micro/levelv/memory_map.yaml` with `gen_linker.py` or maintain a hand-written `link.ld` next to the TFLM generated project.
4. **Operators**: start with **reference kernels**; later swap in CMSIS-NN or custom RISC-V extensions.

## Makefile

```bash
make tinyml_submodules_init
make tinyml_help
```

Full `make run_tflite_micro` is intentionally **not** wired yet — it requires the generated Makefile from TFLM’s build system merged with Level-V’s `riscv-none-elf-` toolchain variables.
