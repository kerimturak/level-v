# Configuration Files — Technical Documentation

## Contents

1. [Overview](#overview)
2. [Verilator Configuration](#verilator-configuration)
3. [ModelSim Configuration](#modelsim-configuration)
4. [Test Configuration](#test-configuration)
5. [JSON files](#json-files)

---

## Overview

### Directory Layout

```
script/config/
├── verilator.json          # Verilator simulator config
├── modelsim.json           # ModelSim config
└── tests/                  # Test profiles (.conf)
    ├── default.conf        # Base profile
    ├── isa.conf            # riscv-tests
    ├── README.md           # Format + behavior
    ├── riscv-dv.json       # RISCV-DV (separate JSON flow)
    └── formal.json         # Formal (separate JSON flow)
```

### Test profile hierarchy

```
default.conf (base, always loaded)
    └── <TEST_CONFIG>.conf   # e.g. isa.conf — overrides / adds keys
```

`make` sets `TEST_CONFIG` from `TEST_TYPE` if unset; override with `TEST_CONFIG=<profile>`. See `script/shell/parse_test_conf.sh` and [script/config/tests/README.md on GitHub](https://github.com/kerimturak/level-v/blob/main/script/config/tests/README.md).

---

## Verilator Configuration

### verilator.json

**File:** `script/config/verilator.json`

#### Full structure

```json
{
  "_comment": "Level RISC-V Verilator Simulation Configuration",

  "simulation": {
    "max_cycles": 100000,
    "timeout": 0,
    "threads": "auto",
    "seed": "auto"
  },

  "build": {
    "mode": "release",
    "jobs": "auto",
    "opt_level": "-O3",
    "cpp_standard": "c++17"
  },

  "trace": {
    "enabled": true,
    "format": "fst",
    "depth": 99,
    "structs": true,
    "params": true,
    "threads": 1,
    "underscore": false
  },

  "coverage": {
    "enabled": true,
    "line": true,
    "toggle": true,
    "user": false
  },

  "optimization": {
    "output_split": 20000,
    "output_split_cfuncs": 5000,
    "unroll_count": 64,
    "unroll_stmts": 30000,
    "x_assign": "fast",
    "x_initial": "fast"
  },

  "features": {
    "vpi": false,
    "hierarchical": false,
    "savable": false,
    "debug_check": false
  },

  "logging": {
    "fast_sim": false,
    "bp_log": false,
    "bp_verbose": false,
    "commit_trace": true,
    "pipeline_log": true,
    "ram_log": true,
    "uart_log": true
  },

  "warnings": {
    "fatal": false,
    "lint": false,
    "style": false,
    "width": false,
    "unused": false,
    "unoptflat": false
  },

  "profiles": { ... }
}
```

#### Section Descriptions

##### simulation

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `max_cycles` | integer | 100000 | Maximum simulation cycles |
| `timeout` | integer | 0 | Wall-clock timeout (seconds, 0=disabled) |
| `threads` | int/auto | auto | Multi-threaded simulation thread count |
| `seed` | int/auto | auto | Random seed |

##### build

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `mode` | string | release | Build mode: debug/release |
| `jobs` | int/auto | auto | Parallel compile job count |
| `opt_level` | string | -O3 | C++ optimization level |
| `cpp_standard` | string | c++17 | C++ standard version |

##### trace

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `enabled` | boolean | true | Waveform trace enable |
| `format` | string | fst | Trace format: fst/vcd |
| `depth` | integer | 99 | Trace depth (0=all) |
| `structs` | boolean | true | Trace structs |
| `params` | boolean | true | Trace parameters |
| `threads` | integer | 1 | Trace writer threads |

##### coverage

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `enabled` | boolean | true | Coverage collection |
| `line` | boolean | true | Line coverage |
| `toggle` | boolean | true | Toggle coverage |
| `user` | boolean | false | User-defined coverage points |

##### optimization

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `output_split` | integer | 20000 | C++ output split size |
| `output_split_cfuncs` | integer | 5000 | Function split size |
| `unroll_count` | integer | 64 | Loop unroll count |
| `unroll_stmts` | integer | 30000 | Max unroll statements |
| `x_assign` | string | fast | X assignment mode: fast/0/1/unique |
| `x_initial` | string | fast | X initial mode: fast/0/1/unique |

##### logging

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `fast_sim` | boolean | false | Fast mode (all logging off) |
| `bp_log` | boolean | false | Branch predictor statistics |
| `bp_verbose` | boolean | false | Per-branch verbose log |
| `commit_trace` | boolean | true | Spike-compatible commit trace |
| `pipeline_log` | boolean | true | Konata pipeline trace |
| `ram_log` | boolean | true | RAM initialization messages |
| `uart_log` | boolean | true | UART TX file log |

#### Profiles

Predefined configuration profiles:

##### fast Profile

```json
"fast": {
  "_description": "Maximum speed, no tracing or logging",
  "simulation": { "threads": "auto" },
  "build": { "mode": "release", "opt_level": "-O3" },
  "trace": { "enabled": false },
  "logging": { "fast_sim": true }
}
```

##### debug Profile

```json
"debug": {
  "_description": "Full debugging with all features",
  "build": { "mode": "debug", "opt_level": "-O0" },
  "trace": { "enabled": true, "depth": 99 },
  "features": { "debug_check": true },
  "logging": { "commit_trace": true, "pipeline_log": true }
}
```

##### coverage Profile

```json
"coverage": {
  "_description": "Coverage collection mode",
  "build": { "mode": "release" },
  "coverage": { "enabled": true, "line": true, "toggle": true },
  "trace": { "enabled": false }
}
```

##### benchmark Profile

```json
"benchmark": {
  "_description": "Benchmark mode with BP logging",
  "simulation": { "max_cycles": 10000000 },
  "build": { "mode": "release", "opt_level": "-O3" },
  "trace": { "enabled": false },
  "logging": { "fast_sim": true, "bp_log": true }
}
```

---

## ModelSim Configuration

### modelsim.json

**File:** `script/config/modelsim.json`

```json
{
  "_comment": "ModelSim/Questa Simulation Configuration",

  "simulation": {
    "max_cycles": 100000,
    "timeout_seconds": 300
  },

  "compilation": {
    "vlog_opts": ["-sv", "-timescale=1ns/1ps"],
    "vopt_opts": ["+acc", "-O4"],
    "coverage": false
  },

  "vsim": {
    "gui": false,
    "do_file": "sim/do/run.do",
    "waveform": true,
    "waveform_file": "build/sim.wlf"
  },

  "logging": {
    "transcript": true,
    "verbose": false
  }
}
```

---

## Test Configuration

Test profiles are `script/config/tests/*.conf` files. The makefile merges `default.conf` first, then `<name>.conf` selected by `TEST_CONFIG`, via `script/shell/parse_test_conf.sh`, and writes `build/.test_config_<name>.mk`.

Full format and key list: [script/config/tests/README.md on GitHub](https://github.com/kerimturak/level-v/blob/main/script/config/tests/README.md).

### Line format (summary)

- `KEY=value` — comments with `#`; blank lines ignored.
- Shortcuts (`MAX_CYCLES`, `SPIKE_ISA`, `COMPARE`, `TRACE`, …) → `CFG_*` makefile variables.
- `CFG_*` lines are written directly into the generated `.mk`.
- Names outside `^[A-Z][A-Z0-9_]*$` are not treated as macros; for macro names, `1` / `true` / `yes` / `on` → `+define+NAME`, otherwise `+define+NAME=value`, or (if falsy) omitted.
- Optional: `CFG_SV_DEFINES=+define+FOO +define+BAR`.

### Example snippets

`default.conf`:

```text
MAX_CYCLES=100000
TIMEOUT=60
SPIKE_ISA=rv32imc_zicsr_zicntr_zifencei
SPIKE_PRIV=m
SPIKE_PC=0x80000000
COMMIT_TRACER=1
LOG_COMMIT=1
```

`isa.conf`:

```text
MAX_CYCLES=10000
KONATA_TRACER=1
```

### Profile table (examples)

| Profile (`.conf`) | Typical use |
|-------------------|-------------|
| `isa` | riscv-tests, lower `MAX_CYCLES` |
| `arch` | riscv-arch-test |
| `coremark` | Long simulation time |
| `custom` | Custom software tests |
| `torture` | Torture / stress |

### JSON (separate flows)

- `riscv-dv.json` — RISC-V DV generator  
- `formal.json` — formal (SymbiYosys / makefile `FORMAL_CONFIG`)

These are outside `.conf` profile merging.

---

## JSON files

Configuration JSON is read directly by the makefile and Python tools. Separate `.schema.json` files are not kept; validity is checked with schemas inside `verilator_config.py` / `modelsim_config.py`.


---

## Configuration Usage

### Makefile integration

The root `makefile` uses both `verilator.json` (and related jq extractions) and, for tests, `parse_test_conf.sh` → `build/.test_config_<TEST_CONFIG>.mk`. Example (abbreviated):

```makefile
# Verilator (abbreviated — real rules live in the makefile)
# MAX_CYCLES, TRACE, … from verilator.json via jq or overrides

# Test profile
TEST_CONFIG ?= default
# TEST_CONFIG_MK := build/.test_config_$(TEST_CONFIG).mk  # parse_test_conf.sh output
```

### Shell script integration

```bash
# Load config
CONFIG=$(cat script/config/verilator.json)

# Extract value
MAX_CYCLES=$(echo "$CONFIG" | jq -r '.simulation.max_cycles')

# Apply profile
if [ -n "$PROFILE" ]; then
    CONFIG=$(echo "$CONFIG" | jq ". * .profiles.$PROFILE")
fi
```

### Python integration

```python
import json

def load_config(config_file, profile=None):
    with open(config_file) as f:
        config = json.load(f)
    
    if profile and 'profiles' in config:
        profile_config = config['profiles'].get(profile, {})
        config = deep_merge(config, profile_config)
    
    return config
```

---

## Local Overrides

### verilator.local.json

For user-specific overrides:

```json
{
  "_comment": "Local overrides (not committed to git)",
  "simulation": {
    "threads": 8
  },
  "trace": {
    "enabled": false
  }
}
```

### .gitignore

```
# Local config overrides
script/config/*.local.json
# Optional: local test profile (example name; not in repo)
# script/config/tests/local.conf
```

---

## Best Practices

1. **Simulator JSON**: Keep `verilator.json` / `modelsim.json` aligned with `verilator_config.py` / `modelsim_config.py`; test profiles are plain `.conf` text.
2. **Test profiles**: Shared settings in `default.conf`; override per suite with `<name>.conf`.
3. **Local overrides**: e.g. `verilator.local.json` for personal sim settings.
4. **Profiles**: Select with `TEST_CONFIG=…`; list with `make list-configs`.
5. **Validation**: Python config readers warn on unknown keys; for `.conf`, rely on the parser plus review.

---

## Summary

Configuration system:

1. **Simulators**: `verilator.json` / `modelsim.json`
2. **Test profiles**: `script/config/tests/*.conf` + `parse_test_conf.sh` + makefile cache
3. **Special JSON**: `riscv-dv.json`, `formal.json` (separate flows)
4. **Local overrides**: e.g. `verilator.local.json`
5. **Tool integration**: Root `makefile`, shell, Python
