# 📦 Test manager system — summary

## ✨ What we built

A **full test management and debug system** for the Level RISC-V project.

---

## 📂 Files created

### 1. Python scripts (core)

#### `script/python/test_manager.py` ⭐
**Main test management CLI**
- Run tests (single, suite, tag-based)
- List and filter tests
- Add/remove tests
- Debug logging integration

**Usage:**
```bash
python3 script/python/test_manager.py run --test rv32ui-p-add
python3 script/python/test_manager.py list --suite benchmarks
python3 script/python/test_manager.py run --tags quick,isa
```

#### `script/python/debug_logger.py` 🔍
**Debug report library**
- Execution flow tracking
- File access monitoring
- Performance metrics (optional psutil)
- Error/warning aggregation
- Hierarchical step tracking

**Features:**
- Timestamp per step
- Full command recording
- Exit codes
- Stdout/stderr logging
- Config snapshots

#### `script/python/debug_viewer.py` 📊
**Debug report viewer and analysis**
- Pretty-print reports
- Errors-only view
- Summary statistics
- Compare two reports
- Colored terminal output

**Usage:**
```bash
python3 script/python/debug_viewer.py
python3 script/python/debug_viewer.py --errors-only
python3 script/python/debug_viewer.py --compare report1.json report2.json
```

---

### 2. Configuration files

#### `script/config/test_registry.json` 📝
**Central test database**

Structure:
```json
{
  "test_suites": {
    "isa_basic": {
      "description": "...",
      "flist": "sim/test/riscv_test_list.flist",
      "tags": ["isa", "compliance", "quick"],
      "enabled": true
    },
    "benchmarks": {
      "tests": {
        "coremark": {
          "config": "script/config/tests/coremark.conf",
          "tags": ["benchmark", "slow"]
        }
      }
    }
  },
  "tag_groups": { ... }
}
```

### 3. Makefile updates

#### `Makefile.verilator` (updated) 🔧

**New variables:**
```makefile
TEST_MANAGER := $(PYTHON) $(SCRIPT_DIR)/python/test_manager.py
DEBUG_VIEWER := $(PYTHON) $(SCRIPT_DIR)/python/debug_viewer.py
DEBUG_ENABLE ?= 1
```

**New targets:**

**Test manager:**
- `test-run` — run one test
- `test-run-suite` — run a suite
- `test-run-tags` — run by tags
- `test-list` — list tests
- `test-add` — add test
- `test-remove` — remove test

**Debug reports:**
- `debug-latest` — show latest report
- `debug-view` — show a specific report
- `debug-errors` — errors only
- `debug-summary` — summary
- `debug-compare` — compare two reports
- `debug-list` — list all reports
- `debug-clean` — clean reports

---

### 4. Documentation

#### `docs/TEST_MANAGER_README.md` 📚
**Full user guide** (100+ sections)
- Detailed examples
- Feature descriptions
- Troubleshooting
- Best practices

#### `docs/QUICKSTART_TESTMANAGER.md` 🚀
**Quick start**
- Up and running in 5 minutes
- Common scenarios
- Pro tips
- Checklist

#### `docs/TEST_MANAGER_SUMMARY.md` (this file)
**System overview**

---

## 🎯 Main features

### 1. ✅ Easy test management

**Before:**
```bash
# Manually edit test list in .flist
vim sim/test/custom_tests.flist
# Add test name by hand
# Run Makefile
make -f Makefile.verilator run TEST_NAME=my_test
```

**After:**
```bash
# Add a test in one command
make -f Makefile.verilator test-add TEST_NAME=my_test SUITE=custom_tests
# Run
make -f Makefile.verilator test-run TEST_NAME=my_test
```

### 2. 🔍 Automatic debug reports

**On every test run:**
- Execution flow is recorded
- All file accesses are logged
- Performance metrics collected
- Errors and warnings aggregated

**Report format:**
```json
{
  "metadata": { "test_name": "...", "timestamp": "..." },
  "execution_flow": [ ... ],
  "files_accessed": { "read": [...], "written": [...] },
  "result": { "status": "PASSED", "duration_total_ms": 17777 },
  "performance": { ... }
}
```

### 3. 🏷️ Tag-based organization

**Group by tags:**
```bash
# Quick tests
make -f Makefile.verilator test-run-tags TAGS=quick

# All compliance tests
make -f Makefile.verilator test-run-tags TAGS=compliance

# Benchmarks
make -f Makefile.verilator test-run-tags TAGS=benchmark
```

### 4. 📊 Debug analysis tools

```bash
# Latest report
make -f Makefile.verilator debug-latest

# Errors only
make -f Makefile.verilator debug-errors

# Compare two runs
make -f Makefile.verilator debug-compare REPORT1=... REPORT2=...
```

---

## 🎨 Sample debug report

```
================================================================================
DEBUG REPORT: rv32ui-p-add
================================================================================

Metadata:
  Test:        rv32ui-p-add
  Target:      run
  Timestamp:   2025-12-13T14:30:22.123456
  Session ID:  a7f3d9e2
  Git:         main@1b39651

Environment:
  CWD:         /home/kerim/level-v
  Python:      3.10.12
  Verilator:   5.028

Result:
  Status:      PASSED
  Exit Code:   0
  Duration:    17.78s

Execution Flow:
────────────────────────────────────────────────────────────────────────────────
  ✓ Step 1: run_test
    Type:     makefile_target
    Duration: 17.78s (100.0%)
    Command:  make -f Makefile.verilator run TEST_NAME=rv32ui-p-add...
    Exit:     0

Files Accessed:
────────────────────────────────────────────────────────────────────────────────
  Read (3 files):
    • script/config/verilator.json
    • build/tests/riscv-tests/mem/rv32ui-p-add.mem
    • rtl/wrapper/level_wrapper.sv

  Written (2 files):
    • build/log/verilator/rv32ui-p-add/commit_trace.log
    • build/log/verilator/rv32ui-p-add/waveform.fst

Performance Metrics:
────────────────────────────────────────────────────────────────────────────────
  CPU Usage:    85.4%
  Memory Peak:  1024.0 MB
  Disk Read:    12.3 MB
  Disk Write:   45.6 MB

Summary Statistics:
────────────────────────────────────────────────────────────────────────────────
  Total Steps:     1
  Total Duration:  17.78s

  Top 3 Slowest Steps:
    1. run_test                        17.78s
```

---

## 📈 Usage statistics

### Suites defined in the test registry:

| Suite | Test count | Status |
|-------|------------|--------|
| isa_basic | 51 | ✓ Active |
| isa_compressed | 1 | ✓ Active |
| isa_multiply | 8 | ✓ Active |
| arch_tests | 91 | ✓ Active |
| benchmarks | 2 | ✓ Active |
| branch_tests | 8 | ✓ Active |
| exception_tests | 2 | ✓ Active |
| csr_tests | 16 | ✓ Active |
| custom_tests | 20 | ✓ Active |
| embench | 16 | ✗ Disabled |
| imperas | 45 | ✗ Disabled |

**Total:** 260 tests (199 active)

---

## 🚀 Quick start

### 1. List tests
```bash
make -f Makefile.verilator test-list
```

### 2. Run a test
```bash
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add
```

### 3. View debug report
```bash
make -f Makefile.verilator debug-latest
```

---

## 💡 Benefits

### ✅ Backward compatible
- All legacy Makefile targets still work
- Existing `.flist` files are used
- Optional debug logging (`DEBUG_ENABLE`)

### ✅ Easier test management
- Add/remove tests in one command
- Tag-based filtering
- Suite-based organization
- Central JSON database

### ✅ Rich debug visibility
- Every step recorded
- File access tracking
- Performance metrics
- Error aggregation
- Report comparison

### ✅ Extensible
- Modular Python
- JSON schema validation
- Easy to extend
- Ready for a plugin model

---

## 🔧 Technical details

### Python dependencies

**Required:**
- Python 3.6+
- Standard library (json, pathlib, subprocess, etc.)

**Optional:**
- `psutil` — performance metrics
  - If missing: "Warning: psutil not available, performance metrics disabled"
  - Install: `pip3 install psutil`

### Directory layout

```
level-v/
├── script/
│   ├── config/
│   │   ├── test_registry.json          ⭐ NEW
│   │   └── tests/
│   │       └── *.conf (test profiles)
│   └── python/
│       ├── test_manager.py             ⭐ NEW
│       ├── debug_logger.py             ⭐ NEW
│       └── debug_viewer.py             ⭐ NEW
├── build/
│   └── debug_reports/                  ⭐ NEW (automatic)
│       ├── run_TIMESTAMP_TEST.json
│       └── latest_TEST.json (symlink)
├── docs/
│   ├── TEST_MANAGER_README.md          ⭐ NEW
│   ├── QUICKSTART_TESTMANAGER.md       ⭐ NEW
│   └── TEST_MANAGER_SUMMARY.md         ⭐ NEW
└── makefile                            (root unified Makefile)
```

---

## 🎯 Next steps (optional)

### 1. Parallel test runs
```python
# Could be added to test_manager.py
def run_tests_parallel(test_names, num_jobs=4):
    # Run in parallel with multiprocessing
```

### 2. Web dashboard
```python
# Flask/FastAPI UI
# View debug reports in the browser
```

### 3. CI/CD integration
```yaml
# .github/workflows/tests.yml
- name: Run tests
  run: make -f Makefile.verilator test-run-tags TAGS=quick
```

### 4. Email reporting
```python
# Email test results
# Auto-notify on failures
```

---

## 📞 Support

For issues, inspect the debug report:
```bash
make -f Makefile.verilator debug-latest
make -f Makefile.verilator debug-errors
```

---

## ✅ Completed features

- [x] Test registry JSON system
- [x] Test manager Python CLI
- [x] Debug logger library
- [x] Debug viewer tool
- [x] Makefile integration
- [x] Tag-based filtering
- [x] Report comparison
- [x] Full documentation
- [x] Quick start guide
- [x] psutil made optional

---

**🎉 The system is ready — you can start testing.**
