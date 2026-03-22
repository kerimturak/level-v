# 🚀 Test manager — quick start

## Test manager in 5 minutes

### 1️⃣ List tests

```bash
make -f Makefile.verilator test-list
```

**Sample output:**
```
Available Test Suites:

  ✓ isa_basic            ( 51 tests) - Basic RISC-V ISA compliance tests
  ✓ benchmarks           (  2 tests) - Performance benchmarks
  ✓ branch_tests         (  8 tests) - Branch predictor tests
  ...
```

### 2️⃣ Run your first test

```bash
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add
```

**What happens:**
- Test runs ✅
- Debug report is created automatically 📝
- Result printed ✅/✗

### 3️⃣ View the debug report

```bash
make -f Makefile.verilator debug-latest
```

**Sample output:**
```
================================================================================
DEBUG REPORT: rv32ui-p-add
================================================================================

Metadata:
  Test:        rv32ui-p-add
  Timestamp:   2025-12-13T14:30:22
  Session ID:  a7f3d9e2

Result:
  Status:      PASSED
  Duration:    17.78s

Execution Flow:
─────────────────────────────────────────────────────────────
  ✓ Step 1: run_test
    Type:     makefile_target
    Duration: 17.78s
```

---

## 🎯 Common scenarios

### Scenario 1: Quick validation

```bash
make -f Makefile.verilator test-run-tags TAGS=quick
make -f Makefile.verilator debug-summary
```

### Scenario 2: Run a benchmark

```bash
make -f Makefile.verilator test-run TEST_NAME=coremark
make -f Makefile.verilator debug-latest TEST_NAME=coremark
```

### Scenario 3: All ISA basic tests

```bash
make -f Makefile.verilator test-run-suite SUITE=isa_basic
make -f Makefile.verilator debug-errors
```

### Scenario 4: Add a new test

```bash
make -f Makefile.verilator test-add \
    TEST_NAME=my_test \
    SUITE=custom_tests
# Prepare my_test.elf / my_test.mem manually
make -f Makefile.verilator test-run TEST_NAME=my_test
```

---

## 📊 Debug reports

### Latest report
```bash
make -f Makefile.verilator debug-latest
```

### Errors only
```bash
make -f Makefile.verilator debug-errors TEST_NAME=rv32ui-p-add
```

### Summary
```bash
make -f Makefile.verilator debug-summary TEST_NAME=rv32ui-p-add
```

### Compare two runs
```bash
make -f Makefile.verilator debug-compare \
    REPORT1=build/debug_reports/run_20251213_143022_test1.json \
    REPORT2=build/debug_reports/run_20251213_150000_test1.json
```

### List all reports
```bash
make -f Makefile.verilator debug-list
```

---

## 🔧 Parameters

### Run parameters

| Variable | Description | Example |
|----------|-------------|---------|
| `TEST_NAME` | Test name | `TEST_NAME=rv32ui-p-add` |
| `SUITE` | Suite | `SUITE=isa_basic` |
| `TAGS` | Tag list | `TAGS=quick,isa` |
| `MAX_CYCLES` | Max cycles | `MAX_CYCLES=50000` |
| `NO_TRACE` | Disable trace | `NO_TRACE=1` |
| `MODE` | Build mode | `MODE=release` |
| `DEBUG_ENABLE` | Debug on/off | `DEBUG_ENABLE=0` |

### Examples

```bash
make -f Makefile.verilator test-run \
    TEST_NAME=rv32ui-p-add \
    MAX_CYCLES=10000

make -f Makefile.verilator test-run \
    TEST_NAME=rv32ui-p-add \
    NO_TRACE=1

make -f Makefile.verilator test-run \
    TEST_NAME=rv32ui-p-add \
    MODE=release

DEBUG_ENABLE=0 make -f Makefile.verilator test-run \
    TEST_NAME=rv32ui-p-add
```

---

## 📁 Important files

### Configuration
- `script/config/test_registry.json` — test database
- `script/config/tests/*.conf` — suite profiles (`TEST_CONFIG`)

### Debug reports
- `build/debug_reports/run_*.json` — reports
- `build/debug_reports/latest_*.json` — symlinks to latest

### Logs
- `build/log/verilator/TEST_NAME/` — test logs
- `build/debug_reports/TIMESTAMP_TEST/step*.log` — step logs

---

## ⚡ Pro tips

### Tip 1: Aliases

```bash
# Add to .bashrc or .zshrc
alias vtest='make -f Makefile.verilator test-run TEST_NAME='
alias vlist='make -f Makefile.verilator test-list'
alias vdebug='make -f Makefile.verilator debug-latest'

vtest rv32ui-p-add
vlist TAGS=quick
vdebug
```

### Tip 2: Tag combinations

```bash
make -f Makefile.verilator test-run-tags TAGS=quick,isa
make -f Makefile.verilator test-run-tags TAGS=benchmark
make -f Makefile.verilator test-run-tags TAGS=compliance
```

### Tip 3: Analyze JSON

```bash
cat build/debug_reports/latest_rv32ui-p-add.json | jq '.result'
cat build/debug_reports/latest_rv32ui-p-add.json | \
    jq '.execution_flow | sort_by(.duration_ms) | reverse | .[0:3]'
cat build/debug_reports/latest_rv32ui-p-add.json | \
    jq '.result.errors'
```

### Tip 4: Batch runs

```bash
for tag in isa_basic isa_compressed isa_multiply; do
    make -f Makefile.verilator test-run-suite SUITE=$tag
    make -f Makefile.verilator debug-summary
done
```

---

## 🐛 Quick troubleshooting

### Test not found
```bash
make -f Makefile.verilator test-list
cat script/config/test_registry.json | jq '.test_suites'
```

### No debug report
```bash
echo $DEBUG_ENABLE
DEBUG_ENABLE=1 make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add
```

### Python error
```bash
python3 -c "from script.python.test_manager import *; print('OK')"
python3 -c "from script.python.debug_logger import *; print('OK')"
```

---

## 📚 More detail

```bash
cat docs/TEST_MANAGER_README.md
make -f Makefile.verilator help
```

---

## ✅ First-time checklist

- [ ] Listed tests
- [ ] Ran first test
- [ ] Viewed debug report
- [ ] Ran a suite
- [ ] Tried tag filtering
- [ ] Added a test
- [ ] Compared debug reports

**All done? Nice work! 🎉**

You can use the test manager effectively from here on.
