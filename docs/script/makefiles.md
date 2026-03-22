# Makefile (unified)

The old `script/makefiles/**/*.mk` fragments were removed; all build / sim / test / synth / lint rules are **merged into the repository root `makefile`**.

## Local override

Optional: `script/makefiles/config/local.mk` — loaded at the end of the root `makefile` via `-include` (silently skipped if missing).

## Navigating the file

The following headings can be searched in `makefile` with `grep`:

| Topic | Example search string |
|------|------------------------|
| Directory and derived paths | `config/paths.mk` or `ROOT_DIR` |
| Toolchain | `RISCV_GCC`, `VERILATOR` |
| RTL list | `rtl/flist.f` → `SV_SOURCES` (`FLIST_SV`) |
| Build profile | `MODE`, `profiles` |
| Test JSON | `test_config` |
| Verilator | `sim/verilator.mk` comment block or `verilate` |
| ModelSim | `sim/modelsim.mk` |
| Test run | `run_test`, `TEST_NAME` |
| CoreMark | `coremark` targets |
| Lint | `lint/lint.mk` |
| Yosys / OpenLane | `synth/` section |

## mkdocs / external documentation

The old “one page per `.mk` file” model no longer applies. For a new **RTL file**, add a line to `rtl/flist.f`; for a new **make target**, edit the root `makefile`.
