# Tool Ecosystem Design Guide

This document explains design principles for the Level project tool ecosystem. It defines how Makefiles, Python, and JSON configuration should work together.

---

## Core principles

### 1. Separation of Concerns

```
┌─────────────────────────────────────────────────────────────────┐
│                         USER                                    │
│                    make simulate T=test                         │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                        MAKEFILE                                 │
│  • Simple interface (make targets)                              │
│  • Path and variable management                                   │
│  • Dependency management                                        │
│  • Short, readable commands                                     │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                         PYTHON                                  │
│  • Complex logic                                                │
│  • Validation and error handling                                │
│  • JSON parsing and merging                                     │
│  • Colored / formatted output                                   │
│  • Platform-independent operations                             │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                          JSON                                   │
│  • All configuration values                                     │
│  • Profile definitions                                          │
│  • Version-control friendly                                     │
│  • Human-readable                                               │
└─────────────────────────────────────────────────────────────────┘
```

---

## 📁 File Organization

```
script/
├── makefiles/           # Optional local.mk (config/); rules live in root makefile
│
├── python/              # Python scripts
│   └── makefile/        # Scripts invoked from the Makefile
│       ├── modelsim_runner.py   # Simulation runner
│       └── modelsim_config.py   # Configuration manager
│
└── config/              # Configuration
    ├── modelsim.json    # ModelSim settings
    ├── verilator.json   # Verilator settings
    └── tests/           # Test profiles (*.conf) + special JSON (riscv-dv, formal)
```

---

## 🔧 Layer Responsibilities

### Makefile layer

**Should do:**
- Simple target definitions (`make simulate`, `make lint`)
- Define and export path variables
- Manage dependency chains
- Invoke Python scripts

**Should not do:**
- Large shell script blocks
- JSON parsing
- Conditional logic (except simple cases)
- Error message formatting

```makefile
# ✅ GOOD: Simple and clear
simulate: compile
	$(PYTHON) $(MODELSIM_RUNNER) \
		--test $(TEST_NAME) \
		--config $(CONFIG_FILE) \
		--log-dir $(LOG_DIR)

# ❌ BAD: Heavy shell block
simulate: compile
	@if [ -f $(MEM_FILE) ]; then \
		echo "Found"; \
		for dir in $(DIRS); do \
			if [ -d $$dir ]; then \
				# 50 more lines of shell...
			fi; \
		done; \
	fi
```

### Python layer

**Should do:**
- Read and merge JSON configuration
- Validation and schema checks
- CLI argument parsing
- Colored, formatted output
- File discovery and path handling
- Subprocess management
- Error handling and reporting

**Should not do:**
- Hardcoded paths or values
- Keep configuration defaults only in code

```python
# ✅ GOOD: From config
sim_time = config.simulation.sim_time

# ❌ BAD: Hardcoded
sim_time = "100us"
```

### JSON layer

**Should contain:**
- All default values
- Profile definitions (debug, fast coverage, etc.)
- Tool-specific settings
- Explanatory comments (`_comment` fields)

**Should not contain:**
- Paths (these come from the Makefile)
- Runtime-only values

```json
{
  "_comment": "ModelSim/Questa Simulation Configuration",
  
  "simulation": {
    "sim_time": "100us",
    "time_resolution": "ns"
  },
  
  "profiles": {
    "fast": {
      "simulation": { "sim_time": "10us" },
      "lint": { "enabled": false }
    },
    "debug": {
      "debug": { "fsmdebug": true }
    }
  }
}
```

---

## 🎨 Colored Console Output

### Color convention

```python
class Color:
    # Status colors
    RED = "\033[0;31m"      # Errors
    GREEN = "\033[0;32m"    # Success
    YELLOW = "\033[1;33m"   # Warnings
    
    # Info colors
    CYAN = "\033[0;36m"     # Info messages
    BLUE = "\033[0;34m"     # Headings
    WHITE = "\033[1;37m"    # Emphasized text
    
    # Styles
    DIM = "\033[2m"         # Dim (secondary info)
    BOLD = "\033[1m"        # Bold
    RESET = "\033[0m"       # Reset
```

### Output formats

```
═══════════════════════════════════════════════════════════
  Level RISC-V Simulation                          [HEADER]
═══════════════════════════════════════════════════════════

▶ Section title                                    [SECTION]
  Key:          Value                              [KEY-VAL]
  Other key:   Other value

[INFO] Info message                                [INFO]
[WARN] Warning message                             [WARN]
[ERROR] Error message                              [ERROR]

════════════════════════════════════════════════════════════
  ✓ Success                                        [SUCCESS]
════════════════════════════════════════════════════════════

════════════════════════════════════════════════════════════
  ✗ Failure                                        [FAILURE]
════════════════════════════════════════════════════════════
```

### Helper functions

```python
def header(title: str, char: str = "═") -> None:
    """Main title banner"""
    width = 60
    print(f"\n{Color.CYAN}{char * width}{Color.RESET}")
    print(f"{Color.CYAN}  {title}{Color.RESET}")
    print(f"{Color.CYAN}{char * width}{Color.RESET}")

def subheader(title: str) -> None:
    """Subheading"""
    print(f"\n{Color.BLUE}▶ {title}{Color.RESET}")

def keyval(key: str, value: str, indent: int = 2) -> None:
    """Key-value pair"""
    spaces = " " * indent
    print(f"{spaces}{Color.DIM}{key}:{Color.RESET} {value}")

def info(msg: str) -> None:
    print(f"{Color.CYAN}[INFO]{Color.RESET} {msg}")

def warn(msg: str) -> None:
    print(f"{Color.YELLOW}[WARN]{Color.RESET} {msg}", file=sys.stderr)

def error(msg: str) -> None:
    print(f"{Color.RED}[ERROR]{Color.RESET} {msg}", file=sys.stderr)

def success(msg: str) -> None:
    print(f"{Color.GREEN}[OK]{Color.RESET} {msg}")
```

### Detecting color support

```python
import sys
import os

def supports_color() -> bool:
    """Return True if the terminal likely supports colors"""
    # No color when piped or redirected to a file
    if not sys.stdout.isatty():
        return False
    
    # NO_COLOR environment variable (standard)
    if os.environ.get("NO_COLOR"):
        return False
    
    # TERM check
    term = os.environ.get("TERM", "")
    if term == "dumb":
        return False
    
    return True

# At script startup
if not supports_color():
    Color.disable()
```

---

## ⚙️ JSON Configuration System

### Defining schema

For each field, define type, default, and valid choices:

```python
CONFIG_SCHEMA = {
    "simulation": {
        "sim_time": {
            "type": "str",
            "default": "100us",
            "pattern": r"^\d+[pnum]?s$",
            "description": "Simulation duration"
        },
        "time_resolution": {
            "type": "str",
            "default": "ns",
            "choices": ["ps", "ns", "us", "ms"],
            "description": "Time resolution"
        }
    }
}
```

### Warnings for unknown parameters

```python
def validate_keys(data: dict, schema: dict, path: str = "") -> List[str]:
    """Emit warnings for unknown keys"""
    warnings = []
    
    for key in data:
        full_path = f"{path}.{key}" if path else key
        
        if key not in schema:
            warnings.append(f"Unknown parameter: '{full_path}'")
        elif isinstance(data[key], dict) and isinstance(schema.get(key), dict):
            warnings.extend(validate_keys(data[key], schema[key], full_path))
    
    return warnings
```

### Profile merge system

```python
def merge_profile(base: dict, profile: dict) -> dict:
    """Merge profile onto base config"""
    result = copy.deepcopy(base)
    
    for key, value in profile.items():
        if isinstance(value, dict) and key in result:
            result[key] = merge_profile(result[key], value)
        else:
            result[key] = value
    
    return result
```

### CLI Override Tracking

```python
@dataclass
class ConfigValue:
    value: Any
    source: str  # "default", "json", "profile", "cli"
    
# Usage
if cli_args.sim_time:
    config.sim_time = ConfigValue(
        value=cli_args.sim_time,
        source="cli"
    )
```

---

## 📋 Makefile → Python Integration

### Standard argument passing

```makefile
# Paths should be absolute
RUNNER_ARGS := \
    --test $(TEST_NAME) \
    --work-dir $(abspath $(WORK_DIR)) \
    --log-dir $(abspath $(LOG_DIR)) \
    --config $(abspath $(CONFIG_FILE))

# Optional arguments
ifdef PROFILE
    RUNNER_ARGS += --profile $(PROFILE)
endif

ifdef SIM_TIME
    RUNNER_ARGS += --sim-time $(SIM_TIME)
endif

simulate:
    $(PYTHON) $(RUNNER) $(RUNNER_ARGS)
```

### Python argparse template

```python
def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Tool Description",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    # Required arguments
    required = parser.add_argument_group("required arguments")
    required.add_argument("--test", required=True, help="Test name")
    
    # Optional arguments
    parser.add_argument("--config", type=Path, help="JSON config file")
    parser.add_argument("--profile", help="Config profile")
    parser.add_argument("--no-color", action="store_true", help="Disable colors")
    
    return parser.parse_args()
```

---

## 🧪 Test and Validation

### Config Validation Target

```makefile
validate_config:
    $(PYTHON) $(CONFIG_MODULE) --validate --config $(CONFIG_FILE)

show_config:
    $(PYTHON) $(CONFIG_MODULE) --show --config $(CONFIG_FILE)
```

### Dry-run mode

```python
parser.add_argument(
    "--dry-run", "-n",
    action="store_true",
    help="Show what would run without executing"
)

# Usage
if args.dry_run:
    print(f"Would run: {' '.join(cmd)}")
    return 0
```

---

## 📊 Output and Logging

### Summary JSON

Emit a summary after each run:

```python
summary = {
    "test": config.test_name,
    "exit_code": exit_code,
    "elapsed_seconds": elapsed,
    "timestamp": datetime.now().isoformat(),
    "config": {
        "source": "json",
        "profile": config.profile_name,
        "cli_overrides": ["sim_time=100ns (JSON: 100us)"]
    },
    "settings": {
        "sim_time": config.sim_time,
        "voptargs": config.voptargs
    }
}

with open(log_dir / "summary.json", "w") as f:
    json.dump(summary, f, indent=2)
```

### Teeing output

```python
# Write to both console and file
with open(log_file, "w") as f:
    process = subprocess.Popen(cmd, stdout=PIPE, stderr=STDOUT, text=True)
    
    for line in process.stdout:
        print(line, end="")  # Console
        f.write(line)        # File
```

---

## ✅ Checklist

When adding a new tool, check:

### Makefile
- [ ] Are targets simple and readable?
- [ ] Are paths absolute via `$(abspath ...)`?
- [ ] Are dependencies declared correctly?
- [ ] Is the help section updated?

### Python
- [ ] Is there JSON config support?
- [ ] Are unknown parameters warned?
- [ ] Is colored output supported?
- [ ] Is there a `--no-color` option?
- [ ] Are error paths handled?
- [ ] Is summary JSON written?
- [ ] Is there a dry-run mode?

### JSON
- [ ] Are all defaults defined?
- [ ] Do profiles make sense?
- [ ] Are `_comment` fields present?
- [ ] Is schema documentation available?

### General
- [ ] Is `make help` updated?
- [ ] Is documentation written?
- [ ] Are usage examples included?

---

## 📖 Example: Adding a New Tool

### 1. Create JSON config

```json
// script/config/newtool.json
{
  "_comment": "New Tool Configuration",
  "version": "1.0",
  
  "defaults": {
    "timeout": 300,
    "verbose": false
  },
  
  "profiles": {
    "quick": { "timeout": 60 },
    "debug": { "verbose": true }
  }
}
```

### 2. Write Python runner

```python
#!/usr/bin/env python3
"""New Tool Runner"""

from pathlib import Path
import argparse
import json
import subprocess

# Import or define Color and helpers...

def main():
    args = parse_args()
    
    if not supports_color() or args.no_color:
        Color.disable()
    
    config = load_config(args.config, args.profile)
    
    header("New Tool")
    # ... work
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
```

### 3. Add Makefile target

```makefile
# New section in root makefile (example)

NEWTOOL_RUNNER := $(SCRIPT_DIR)/python/makefile/newtool_runner.py
NEWTOOL_CONFIG := $(SCRIPT_DIR)/config/newtool.json

newtool:
    $(PYTHON) $(NEWTOOL_RUNNER) \
        --config $(NEWTOOL_CONFIG) \
        $(if $(PROFILE),--profile $(PROFILE))

.PHONY: newtool
```

### 4. Add to root `makefile`

Add new targets to the repository root `makefile` next to the appropriate `# ====== ... ======` section.

---

## 🔍 Debug Logging

Each Python runner may emit detailed debug logs to simplify troubleshooting.

### Using the debug logger

```python
from debug_logger import create_logger, DebugLogger

# Create logger
logger = create_logger(
    tool_name="verilator",      # or "modelsim"
    log_dir=config.log_dir,
    debug_enabled=True          # or LEVEL_DEBUG=1
)

# Start section
logger.section("Configuration")

# Log parameters (with source)
logger.param("test_name", "rv32ui-p-add", source="cli")
logger.param("max_cycles", 100000, source="json")
logger.param("trace_enabled", True, source="default")

# Log command
logger.command(["vsim", "-c", ...], "ModelSim simulation")

# File check
logger.file_check(Path("/path/to/file.mem"), "Memory file")

# Save result
logger.result(success=True, exit_code=0, message="Completed")
logger.save()
```

### Enabling debug mode

```bash
# Via environment variable
LEVEL_DEBUG=1 make run_verilator TEST_NAME=rv32ui-p-add

# Via CLI flag
python verilator_runner.py --test rv32ui-p-add --debug

# Also echo to console
LEVEL_DEBUG=1 LEVEL_DEBUG_ECHO=1 make simulate TEST_NAME=test
```

### Debug log formats

Each run produces two formats:

**1. Text log (human-readable)**
```
results/logs/verilator/test/debug_verilator_20251206_180823.log
results/logs/verilator/test/debug_verilator_latest.log  # Latest run
```

**2. JSON log (machine-readable)**
```
results/logs/verilator/test/debug_verilator_20251206_180823.json
results/logs/verilator/test/debug_verilator_latest.json
```

### Debug log contents

```
================================================================================
  Level RISC-V — VERILATOR Debug Log
================================================================================
  Started: 2025-12-06 18:08:23
  CWD:     /home/kerim/level-v
  Python:  3.10.12
================================================================================

┌──────────────────────────────────────────────────────────────────────────────┐
│ CLI Arguments                                                                │
└──────────────────────────────────────────────────────────────────────────────┘
  [CLI ] test                      = rv32uc-p-rvc
  [CLI ] max_cycles                = 10000
  [CLI ] profile                   = None

┌──────────────────────────────────────────────────────────────────────────────┐
│ Run Configuration                                                            │
└──────────────────────────────────────────────────────────────────────────────┘
  [MERG] test_name                 = rv32uc-p-rvc
  [MERG] max_cycles                = 10000
  [MERG] cli_overrides             = ["max_cycles=10000 (JSON: 100000)"]

┌──────────────────────────────────────────────────────────────────────────────┐
│ Command                                                                      │
└──────────────────────────────────────────────────────────────────────────────┘
  ▶ Command: Verilator simulation
    $ /path/to/Vlevel_wrapper 10000 +INIT_FILE=test.mem ...

┌──────────────────────────────────────────────────────────────────────────────┐
│ Results                                                                      │
└──────────────────────────────────────────────────────────────────────────────┘
  [EXEC] exit_code                 = 0
  [EXEC] elapsed_seconds           = 0.21
  ✅ Simulation passed: rv32uc-p-rvc

================================================================================
  ✅ SUCCESS - Simulation completed successfully
================================================================================
```

### Parameter sources

The debug log shows where each parameter came from:

| Tag | Description |
|-----|-------------|
| `[CLI ]` | From command line |
| `[JSON]` | From JSON config |
| `[DEF ]` | Default value |
| `[MERG]` | Merged final value |
| `[FOUN]` | Auto-discovered file |
| `[EXEC]` | Determined at runtime |
| `[OVR ]` | Overridden |

---

## 🔗 Related files

- `script/python/makefile/debug_logger.py` - Debug logger module
- `script/python/makefile/modelsim_runner.py` - ModelSim runner (with logger)
- `script/python/makefile/verilator_runner.py` - Verilator runner (with logger)
- `script/python/makefile/test_runner.py` - Test pipeline runner (with logger)
- `script/python/makefile/modelsim_config.py` - Example config manager
- `script/config/modelsim.json` - Example JSON config
- Root `makefile` — ModelSim / test pipeline targets (`grep "modelsim\\|run_test" makefile`)

---

## 🧪 Test runner pipeline

### Overview

`test_runner.py` is the Python module that orchestrates the test flow end-to-end. It can be invoked from the Makefile with `USE_PYTHON=1`:

```bash
# Via Makefile
make run T=rv32ui-p-add USE_PYTHON=1

# With debug
LEVEL_DEBUG=1 make run T=rv32ui-p-add USE_PYTHON=1

# Direct Python
python3 script/python/makefile/test_runner.py --test-name rv32ui-p-add --debug
```

### Pipeline stages

```
┌─────────────────────────────────────────────────────────────────┐
│                      TEST PIPELINE                              │
├─────────────────────────────────────────────────────────────────┤
│  1️⃣ TEST PREPARATION                                           │
│     - Create log directories                                    │
│     - Check required files (ELF, MEM, ADDR)                     │
│     - Start report file                                         │
├─────────────────────────────────────────────────────────────────┤
│  2️⃣ RTL SIMULATION                                             │
│     - Invoke Verilator or ModelSim runner                       │
│     - Collect simulation outputs                                │
│     - Produce commit_trace.log                                  │
├─────────────────────────────────────────────────────────────────┤
│  3️⃣ SPIKE GOLDEN REFERENCE (optional)                         │
│     - Run Spike ISS on the same ELF                             │
│     - Produce golden commit log                                 │
├─────────────────────────────────────────────────────────────────┤
│  4️⃣ LOG COMPARISON (optional)                                 │
│     - Compare RTL and Spike commit logs                         │
│     - If different, emit detailed report                          │
├─────────────────────────────────────────────────────────────────┤
│  5️⃣ REPORT GENERATION                                         │
│     - Report test outcome                                       │
│     - Save debug logs                                           │
└─────────────────────────────────────────────────────────────────┘
```

### Makefile integration

The Python runner is integrated in `run_test.mk` as follows:

```makefile
# Choose Python or legacy Makefile runner
ifeq ($(USE_PYTHON),1)
run: run_python
else
run: run_make
endif

# Python-based test runner
run_python:
    python3 $(TEST_RUNNER_SCRIPT) \
        --test-name "$(TEST_NAME)" \
        --test-type "$(TEST_TYPE)" \
        --simulator "$(SIM)" \
        --build-dir "$(BUILD_DIR)" \
        --max-cycles $(MAX_CYCLES) \
        $(if $(filter 1,$(LOG_COMMIT)),--log-commit,) \
        $(if $(filter 1,$(CFG_SPIKE)),--enable-spike,--no-spike)
```

### Test Type Auto-Detection

`test_runner.py` automatically detects the test type:

| Pattern | Test Type |
|---------|-----------|
| `rv32ui-p-*`, `rv32um-p-*` | `isa` |
| `I-ADD-01`, `M-MUL-01` | `arch` or `imperas` |
| `dhrystone`, `coremark` | `bench` |
| `aha-mont64`, `crc32` | `embench` |

### Quick mode

Use `--quick` or `--no-spike` for faster runs:

```bash
# RTL simulation only; no Spike or log compare
make run T=rv32ui-p-add USE_PYTHON=1 CFG_SPIKE=0

# Python quick mode directly
python3 test_runner.py --test-name rv32ui-p-add --quick
```

### Debug log example

```
================================================================================
  Level RISC-V — TEST_RUNNER Debug Log
================================================================================
  Started: 2025-12-06 18:20:40
  CWD:     /home/kerim/level-v
  Python:  3.10.12
================================================================================

┌──────────────────────────────────────────────────────────────────────────────┐
│ CLI Arguments                                                                │
└──────────────────────────────────────────────────────────────────────────────┘
  [CLI ] test_name                 = rv32ui-p-add
  [CLI ] test_type                 = isa
  [CLI ] simulator                 = verilator
  [CLI ] max_cycles                = 10000

┌──────────────────────────────────────────────────────────────────────────────┐
│ Resolved Configuration                                                       │
└──────────────────────────────────────────────────────────────────────────────┘
  [RESO] root_dir                  = /home/kerim/level-v
  [RESO] build_dir                 = /home/kerim/level-v/build
  [RESO] skip_spike                = False
  [RESO] skip_compare              = False

┌──────────────────────────────────────────────────────────────────────────────┐
│ Test Pipeline Start                                                          │
└──────────────────────────────────────────────────────────────────────────────┘
  [CONF] test_name                 = rv32ui-p-add
  [CONF] simulator                 = verilator
  ...
```
