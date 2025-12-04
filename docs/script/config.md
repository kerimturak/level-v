# Configuration Files - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Verilator Configuration](#verilator-configuration)
3. [ModelSim Configuration](#modelsim-configuration)
4. [Test Configuration](#test-configuration)
5. [JSON Schema Validation](#json-schema-validation)

---

## Genel Bakış

### Dizin Yapısı

```
script/config/
├── verilator.json          # Verilator simulator config
├── verilator.schema.json   # Verilator schema
├── modelsim.json           # ModelSim config
├── modelsim.schema.json    # ModelSim schema
└── tests/                  # Test suite configs
    ├── default.json        # Base configuration
    ├── tests.schema.json   # Test config schema
    ├── isa.json            # riscv-tests config
    ├── arch.json           # riscv-arch-test config
    ├── imperas.json        # Imperas tests config
    ├── coremark.json       # CoreMark config
    ├── dhrystone.json      # Dhrystone config
    ├── embench.json        # Embench config
    ├── bench.json          # General benchmark config
    ├── csr.json            # CSR test config
    ├── custom.json         # Custom test config
    ├── branch_test.json    # Branch predictor test config
    ├── torture.json        # Torture test config
    ├── riscv-dv.json       # RISCV-DV config
    ├── formal.json         # Formal verification config
    └── README.md           # Config documentation
```

### Configuration Hierarchy

```
default.json (base)
    ├── isa.json (extends default)
    ├── arch.json (extends default)
    ├── coremark.json (extends default)
    └── ... other test configs
```

---

## Verilator Configuration

### verilator.json

**Dosya:** `script/config/verilator.json`

#### Tam Yapı

```json
{
  "$schema": "./verilator.schema.json",
  "_comment": "CERES RISC-V Verilator Simulation Configuration",

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

#### Section Açıklamaları

##### simulation

| Field | Type | Default | Açıklama |
|-------|------|---------|----------|
| `max_cycles` | integer | 100000 | Maximum simülasyon cycle'ı |
| `timeout` | integer | 0 | Wall-clock timeout (saniye, 0=devre dışı) |
| `threads` | int/auto | auto | Multi-threaded simulation thread sayısı |
| `seed` | int/auto | auto | Random seed |

##### build

| Field | Type | Default | Açıklama |
|-------|------|---------|----------|
| `mode` | string | release | Build mode: debug/release |
| `jobs` | int/auto | auto | Parallel compile job sayısı |
| `opt_level` | string | -O3 | C++ optimization level |
| `cpp_standard` | string | c++17 | C++ standard version |

##### trace

| Field | Type | Default | Açıklama |
|-------|------|---------|----------|
| `enabled` | boolean | true | Waveform trace enable |
| `format` | string | fst | Trace format: fst/vcd |
| `depth` | integer | 99 | Trace depth (0=all) |
| `structs` | boolean | true | Trace structs |
| `params` | boolean | true | Trace parameters |
| `threads` | integer | 1 | Trace writer threads |

##### coverage

| Field | Type | Default | Açıklama |
|-------|------|---------|----------|
| `enabled` | boolean | true | Coverage collection |
| `line` | boolean | true | Line coverage |
| `toggle` | boolean | true | Toggle coverage |
| `user` | boolean | false | User-defined coverage points |

##### optimization

| Field | Type | Default | Açıklama |
|-------|------|---------|----------|
| `output_split` | integer | 20000 | C++ output split size |
| `output_split_cfuncs` | integer | 5000 | Function split size |
| `unroll_count` | integer | 64 | Loop unroll count |
| `unroll_stmts` | integer | 30000 | Max unroll statements |
| `x_assign` | string | fast | X assignment mode: fast/0/1/unique |
| `x_initial` | string | fast | X initial mode: fast/0/1/unique |

##### logging

| Field | Type | Default | Açıklama |
|-------|------|---------|----------|
| `fast_sim` | boolean | false | Fast mode (tüm log'lar kapalı) |
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

**Dosya:** `script/config/modelsim.json`

```json
{
  "$schema": "./modelsim.schema.json",
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

### default.json - Base Configuration

**Dosya:** `script/config/tests/default.json`

Tüm test config'lerinin temel aldığı base configuration:

```json
{
  "$schema": "./tests.schema.json",
  "_comment": "CERES RISC-V Default Test Configuration",

  "simulation": {
    "max_cycles": 100000,
    "timeout_seconds": 60,
    "build_threads": "auto",
    "sim_threads": 16
  },

  "comparison": {
    "enabled": true,
    "spike_enabled": true
  },

  "spike": {
    "enabled": true,
    "isa": "rv32imc_zicsr_zicntr_zifencei",
    "priv": "m",
    "pc": "0x80000000",
    "processors": 1,
    "memory_mb": 256,
    "triggers": 1,
    "pmp_regions": 0,
    "pmp_granularity": 4,
    "misaligned": false,
    "big_endian": false,
    "halted": false,
    "log_commits": true,
    "log_cache_miss": false,
    "debug_mode": true,
    "instructions_limit": 0,
    "real_time_clint": false,
    "blocksz": 64
  },

  "defines": {
    "COMMIT_TRACER": true,
    "KONATA_TRACER": false,
    "LOG_COMMIT": true,
    "LOG_RAM": false,
    "LOG_UART": false,
    "LOG_BP": true,
    "SIM_FAST": false,
    "SIM_UART_MONITOR": false
  }
}
```

### isa.json - riscv-tests Configuration

```json
{
  "$schema": "./tests.schema.json",
  "_comment": "riscv-tests ISA compliance",
  "extends": "default",
  "test_list": "sim/test/riscv_test_list.flist",
  "simulation": {
    "max_cycles": 10000
  },
  "defines": {
    "COMMIT_TRACER": true,
    "KONATA_TRACER": true,
    "LOG_COMMIT": true,
    "LOG_RAM": false,
    "LOG_UART": false,
    "LOG_BP": true,
    "SIM_FAST": false,
    "SIM_UART_MONITOR": false
  }
}
```

### coremark.json - CoreMark Configuration

```json
{
  "$schema": "./tests.schema.json",
  "_comment": "CoreMark benchmark",
  "extends": "default",
  "test_list": "sim/test/coremark_test_list.flist",
  "simulation": {
    "max_cycles": 50000000,
    "build_threads": "auto",
    "sim_threads": 16
  },
  "defines": {
    "COMMIT_TRACER": true,
    "KONATA_TRACER": false,
    "LOG_COMMIT": true,
    "SIM_FAST": true,
    "LOG_UART": true,
    "LOG_BP": true,
    "SIM_UART_MONITOR": true
  }
}
```

### Test Config Özellikleri

| Config | max_cycles | Özellikler |
|--------|------------|------------|
| `isa.json` | 10000 | KONATA_TRACER=true, hızlı ISA testleri |
| `arch.json` | 50000 | Architecture compliance |
| `imperas.json` | 100000 | Extended compliance |
| `coremark.json` | 50000000 | SIM_FAST=true, UART_MONITOR=true |
| `dhrystone.json` | 10000000 | Benchmark mode |
| `embench.json` | 5000000 | Embedded benchmark suite |
| `csr.json` | 10000 | CSR test specific |
| `torture.json` | 1000000 | Random instruction torture |
| `formal.json` | N/A | Formal verification settings |

---

## JSON Schema Validation

### tests.schema.json

Test configuration'ların validation schema'sı:

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "CERES RISC-V Test Configuration",
  "description": "Configuration schema for test suites",
  "type": "object",
  "properties": {
    "$schema": { "type": "string" },
    "_comment": { "type": "string" },
    
    "test_list": {
      "type": "string",
      "description": "Path to test list file"
    },
    
    "simulation": {
      "type": "object",
      "properties": {
        "max_cycles": { 
          "type": "integer", 
          "minimum": 1 
        },
        "timeout_seconds": { 
          "type": "integer", 
          "minimum": 0 
        },
        "parallel_jobs": {
          "oneOf": [
            {"type": "integer", "minimum": 1}, 
            {"const": "auto"}
          ]
        },
        "build_threads": {
          "oneOf": [
            {"type": "integer", "minimum": 1}, 
            {"const": "auto"}
          ]
        },
        "sim_threads": {
          "oneOf": [
            {"type": "integer", "minimum": 1}, 
            {"const": "auto"}
          ]
        }
      }
    },
    
    "comparison": {
      "type": "object",
      "properties": {
        "enabled": { "type": "boolean" },
        "spike_enabled": { "type": "boolean" }
      }
    },
    
    "defines": {
      "type": "object",
      "properties": {
        "SIM_FAST": { "type": "boolean" },
        "LOG_COMMIT": { "type": "boolean" },
        "LOG_PIPELINE": { "type": "boolean" },
        "LOG_RAM": { "type": "boolean" },
        "LOG_UART": { "type": "boolean" },
        "LOG_BP": { "type": "boolean" },
        "LOG_BP_VERBOSE": { "type": "boolean" },
        "KONATA_TRACER": { "type": "boolean" },
        "COMMIT_TRACER": { "type": "boolean" }
      }
    }
  }
}
```

### Schema Kullanımı

```bash
# JSON validate etme (jq ile)
jq --slurpfile schema tests.schema.json 'empty' isa.json

# VS Code'da otomatik validation
# "$schema" field ile automatic validation
```

---

## Configuration Usage

### Makefile Entegrasyonu

```makefile
# Config file loading
CONFIG_FILE ?= script/config/verilator.json

# Parse config with jq
MAX_CYCLES := $(shell jq -r '.simulation.max_cycles' $(CONFIG_FILE))
TRACE_ENABLED := $(shell jq -r '.trace.enabled' $(CONFIG_FILE))

# Apply profile
ifdef PROFILE
  CONFIG := $(shell jq -s '.[0] * .[0].profiles.$(PROFILE)' $(CONFIG_FILE))
endif
```

### Shell Script Entegrasyonu

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

### Python Entegrasyonu

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

Kullanıcı-specific override'lar için:

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
script/config/tests/*.local.json
```

---

## Best Practices

1. **Schema Kullanımı**: Her JSON dosyasında `$schema` field kullanın
2. **Extends Kullanımı**: Tekrar eden config'ler için `extends` kullanın
3. **Local Overrides**: Personal settings için `.local.json` kullanın
4. **Comments**: `_comment` field ile documentation ekleyin
5. **Profiles**: Farklı use-case'ler için profile tanımlayın
6. **Validation**: CI/CD'de schema validation yapın

---

## Özet

Configuration system:

1. **JSON Format**: Human-readable, easy to edit
2. **Schema Validation**: JSON Schema ile validation
3. **Profiles**: Predefined configuration sets
4. **Inheritance**: `extends` ile config reuse
5. **Local Overrides**: User-specific overrides
6. **Tool Integration**: Makefile, shell, Python support
