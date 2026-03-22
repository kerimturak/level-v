# Level RISC-V Test Manager & Debug System

## 📋 Contents

1. [Overview](#overview)
2. [Features](#features)
3. [Quick start](#quick-start)
4. [Using the test manager](#using-the-test-manager)
5. [Debug report system](#debug-report-system)
6. [Test registry](#test-registry)
7. [Makefile integration](#makefile-integration)
8. [Examples](#examples)
9. [Troubleshooting](#troubleshooting)

---

## 🎯 Overview

This is a modern test management and debug stack for the Level RISC-V project. Highlights:

- **JSON-based test registry:** Manage all tests from one JSON file
- **Python CLI:** Run, list, add, and remove tests easily
- **Automatic debug reports:** Detailed report for every test run
- **Tag-based filtering:** Run tests by tags
- **Makefile integration:** Works with your existing Makefile flow

---

## ✨ Features

### 1. Test management
- ✅ Define suites in JSON
- ✅ Group tests by tags
- ✅ Add/remove tests in one command
- ✅ Filter test lists
- ✅ Parallel runs (planned)

### 2. Debug reports
- ✅ Detailed per-step log
- ✅ Execution flow tracking
- ✅ File access monitoring
- ✅ Performance metrics
- ✅ Error/warning aggregation
- ✅ Report comparison

### 3. Makefile integration
- ✅ Backward compatible
- ✅ New test-manager targets
- ✅ Debug report viewing targets
- ✅ Easy enable/disable of debug

---

## 🚀 Quick start

### Step 1: List tests

Show available suites:

```bash
make -f Makefile.verilator test-list
```

### Step 2: Run a test

Run one test (debug on):

```bash
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add
```

### Step 3: View the debug report

```bash
make -f Makefile.verilator debug-latest
```

---

## 📦 Using the test manager

### Running tests

#### Single test
```bash
# Via Makefile
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add

# Direct Python CLI
python3 script/python/test_manager.py run --test rv32ui-p-add

# Extra parameters
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add MAX_CYCLES=50000
```

#### Test suite
```bash
# ISA basic suite
make -f Makefile.verilator test-run-suite SUITE=isa_basic

# Benchmark suite
make -f Makefile.verilator test-run-suite SUITE=benchmarks
```

#### Tag-based runs
```bash
# Quick tests
make -f Makefile.verilator test-run-tags TAGS=quick

# ISA and compliance
make -f Makefile.verilator test-run-tags TAGS=isa,compliance

# Benchmarks
make -f Makefile.verilator test-run-tags TAGS=benchmark
```

### Listing tests

```bash
# All suites
make -f Makefile.verilator test-list

# One suite
make -f Makefile.verilator test-list SUITE=benchmarks

# Filter by tag
make -f Makefile.verilator test-list TAGS=quick
```

### Adding/removing tests

```bash
# Add test
make -f Makefile.verilator test-add \
    TEST_NAME=my_new_test \
    SUITE=custom_tests

# Add with config
make -f Makefile.verilator test-add \
    TEST_NAME=my_test \
    SUITE=custom_tests \
    TEST_CONFIG=custom

# Remove test
make -f Makefile.verilator test-remove TEST_NAME=my_test
```

---

## 🔍 Debug report system

### Report structure

Each run produces a report with:

```json
{
  "metadata": {
    "test_name": "rv32ui-p-add",
    "timestamp": "2025-12-13T14:30:22",
    "git_commit": "1b39651",
    "session_id": "a7f3d9e2"
  },
  "execution_flow": [
    {
      "step": 1,
      "type": "makefile_target",
      "name": "build",
      "command": "verilator --cc ...",
      "duration_ms": 5432,
      "exit_code": 0
    }
  ],
  "result": {
    "status": "PASSED",
    "duration_total_ms": 17777
  }
}
```

### Viewing reports

```bash
# Latest report
make -f Makefile.verilator debug-latest

# Latest for a test
make -f Makefile.verilator debug-latest TEST_NAME=rv32ui-p-add

# Specific file
make -f Makefile.verilator debug-view \
    REPORT=build/debug_reports/run_20251213_143022_rv32ui-p-add.json

# Errors only
make -f Makefile.verilator debug-errors TEST_NAME=rv32ui-p-add

# Summary stats
make -f Makefile.verilator debug-summary TEST_NAME=rv32ui-p-add
```

### Comparing reports

```bash
make -f Makefile.verilator debug-compare \
    REPORT1=build/debug_reports/run_20251213_143022_rv32ui-p-add.json \
    REPORT2=build/debug_reports/run_20251213_150000_rv32ui-p-add.json
```

### List reports

```bash
# List all
make -f Makefile.verilator debug-list

# Clean reports
make -f Makefile.verilator debug-clean
```

### Disabling debug

```bash
# Run without debug
DEBUG_ENABLE=0 make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add

# Python CLI
python3 script/python/test_manager.py run --test rv32ui-p-add --no-debug
```

---

## 📝 Test registry

Registry file: `script/config/test_registry.json`

### Structure

```json
{
  "test_suites": {
    "isa_basic": {
      "description": "Basic RISC-V ISA compliance tests",
      "config": "script/config/tests/default.conf",
      "flist": "sim/test/riscv_test_list.flist",
      "tags": ["isa", "compliance", "quick"],
      "enabled": true
    },
    "benchmarks": {
      "description": "Performance benchmarks",
      "tests": {
        "coremark": {
          "description": "CoreMark CPU benchmark",
          "config": "script/config/tests/coremark.conf",
          "tags": ["benchmark", "performance", "slow"],
          "enabled": true,
          "max_cycles": 50000000
        }
      }
    }
  }
}
```

### Adding a suite

Edit `test_registry.json`:

```json
{
  "test_suites": {
    "my_custom_suite": {
      "description": "My custom test suite",
      "config": "script/config/tests/custom.conf",
      "flist": "sim/test/custom_tests.flist",
      "tags": ["custom", "experimental"],
      "enabled": true
    }
  }
}
```

### Tag groups

Logical tag groups:

```json
{
  "tag_groups": {
    "quick": {
      "description": "Fast tests for quick validation",
      "includes": ["isa", "quick"]
    },
    "full": {
      "description": "Full regression suite",
      "includes": ["isa", "compliance", "arch", "benchmark"]
    }
  }
}
```

---

## 🔧 Makefile integration

### New targets

#### Test manager
- `test-run` — run one test
- `test-run-suite` — run suite
- `test-run-tags` — run by tags
- `test-list` — list tests
- `test-add` — add test
- `test-remove` — remove test

#### Debug reports
- `debug-latest` — latest report
- `debug-view` — specific report
- `debug-errors` — errors only
- `debug-summary` — summary
- `debug-compare` — compare two
- `debug-list` — list all
- `debug-clean` — clean

### Compatibility with existing targets

Legacy targets still work:

```bash
# Old way — still works
make -f Makefile.verilator run TEST_NAME=rv32ui-p-add
make -f Makefile.verilator isa
make -f Makefile.verilator verilator-coremark

# New way — with debug
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add
make -f Makefile.verilator test-run-suite SUITE=isa_basic
```

---

## 📚 Examples

### Example 1: Quick validation

```bash
make -f Makefile.verilator test-list TAGS=quick
make -f Makefile.verilator test-run-tags TAGS=quick
make -f Makefile.verilator debug-latest
```

### Example 2: Performance benchmark

```bash
make -f Makefile.verilator test-run TEST_NAME=coremark
REPORT1=$(ls -t build/debug_reports/run_*_coremark.json | head -1)
make -f Makefile.verilator test-run TEST_NAME=coremark MODE=release
REPORT2=$(ls -t build/debug_reports/run_*_coremark.json | head -1)
make -f Makefile.verilator debug-compare REPORT1=$REPORT1 REPORT2=$REPORT2
```

### Example 3: Debugging failures

```bash
make -f Makefile.verilator test-run TEST_NAME=problematic_test
make -f Makefile.verilator debug-errors TEST_NAME=problematic_test
make -f Makefile.verilator debug-latest TEST_NAME=problematic_test
# Report shows which files were created
```

### Example 4: New test

```bash
make -f Makefile.verilator test-add \
    TEST_NAME=my_custom_test \
    SUITE=custom_tests \
    TEST_CONFIG=custom
# Prepare ELF/MEM under build/tests/...
make -f Makefile.verilator test-run TEST_NAME=my_custom_test
make -f Makefile.verilator debug-latest TEST_NAME=my_custom_test
```

---

## 🐛 Troubleshooting

### No debug report

**Problem:** Report not created.

**Fix:**
```bash
echo $DEBUG_ENABLE  # should be 1
DEBUG_ENABLE=1 make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add
python3 -c "from script.python.debug_logger import DebugLogger; print('OK')"
```

### Test registry not found

**Problem:** `Error: Test registry not found`

**Fix:**
```bash
ls -la script/config/test_registry.json
cp script/config/test_registry.json.example script/config/test_registry.json
```

### Test not found

**Problem:** Suite or test missing.

**Fix:**
```bash
make -f Makefile.verilator test-list
make -f Makefile.verilator test-list SUITE=isa_basic
cat script/config/test_registry.json | jq '.test_suites'
```

### Python import error

**Problem:** `ImportError: No module named 'psutil'`

**Fix:**
```bash
pip3 install psutil
pip3 install -r requirements.txt
```

### Makefile target missing

**Problem:** New targets not recognized.

**Fix:**
```bash
grep -n "test-run:" Makefile.verilator
make -f Makefile.verilator clean
make -f Makefile.verilator help | grep test-run
```

---

## 🔗 Related files

### Python
- `script/python/test_manager.py` — main CLI
- `script/python/debug_logger.py` — logging library
- `script/python/debug_viewer.py` — viewer

### Configuration
- `script/config/test_registry.json` — registry
- `script/config/tests/*.conf` — suite profiles (`TEST_CONFIG` / `parse_test_conf.sh`)

### Makefile
- `Makefile.verilator` — main Verilator makefile (updated)

### Docs
- `docs/TEST_MANAGER_README.md` — this file

---

## 📞 Support

1. Inspect debug report: `make debug-latest`
2. Check logs: `build/debug_reports/*/`
3. Validate registry: `cat script/config/test_registry.json | jq`

---

## 🎉 Summary

With this system you can:

✅ Manage tests from one place  
✅ Keep a detailed record of every run  
✅ Find and fix issues faster  
✅ Add/remove tests in seconds  
✅ Adopt new features without breaking old workflows  

**Happy testing! 🚀**
