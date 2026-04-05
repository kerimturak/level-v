# MLPerf Tiny — Level-V integration (scaffold)

Upstream: [github.com/mlcommons/tiny](https://github.com/mlcommons/tiny) (add under `subrepo/mlperf-tiny`).

## Repo layout (upstream)

- Benchmark rules, reference implementations, and submission docs live in the MLCommons repo.
- A runnable SoC binary is **not** produced by cloning alone: you need a **harness** (often TensorFlow Lite Micro) and a **RISC-V bare-metal port** similar to `env/coremark/levelv/`.

## This directory

| Path | Purpose |
|------|---------|
| `levelv/memory_map.yaml` | Starting point for `script/python/gen_linker.py` when you add a TinyML ELF target. Tune `ram.length` / heap to match BRAM and TFLM arena. |

## Makefile

```bash
make tinyml_submodules_init   # fetch subrepo/mlperf-tiny
make tinyml_status
make tinyml_help              # lists CoreMark + TinyML commands
```

## Next steps (for a paper-quality flow)

1. Finish `tflite-micro` Level-V platform target (see `env/tflite-micro/README.md`).
2. Map MLPerf Tiny v1.x models to TFLM or reference C.
3. Add a `make` target that builds a `.mem` file and `run_verilator` like `run_coremark`.
