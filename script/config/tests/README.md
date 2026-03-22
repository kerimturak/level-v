# Test profiles (`.conf`)

The makefile merges `default.conf` and `<TEST_CONFIG>.conf` and emits `build/.test_config_<name>.mk` via `script/shell/parse_test_conf.sh`.

## Line format

- `KEY=value` — `#` starts a comment; blank lines are ignored.
- **`CFG_*`** — written straight through as Makefile variables.
- **Shortcut keys** — `MAX_CYCLES`, `SPIKE_ISA`, `COMPARE`, `SPIKE`, `MODE`, `TRACE`, … map internally to `CFG_*` (see the parser).
- **Other `ALL_CAPS` names** — become RTL `+define+NAME` when the value is truthy (`1` / `true` / `yes` / `on`), or `+define+NAME=value` otherwise.
- Optional: `CFG_SV_DEFINES=+define+FOO +define+BAR` — merged with generated defines.

Example: a `SYNTHESIS=1` line becomes `+define+SYNTHESIS` for Verilator/ModelSim when the profile is loaded and wired into the `SV_DEFINES` chain.

## CLI

Variables from the shell (`make MAX_CYCLES=50000`, `SIM_FAST=1`, …) override assignments of the same name coming from `.conf`, per normal GNU Make rules (unless `override` is used).

Pick a profile with `TEST_CONFIG=<name>` (`script/config/tests/<name>.conf`, merged with `default.conf`).

## Standalone JSON

- `riscv-dv.json` — RISC-V DV generator settings  
- `formal.json` — formal flow  

These sit outside the `.conf` merge system.
