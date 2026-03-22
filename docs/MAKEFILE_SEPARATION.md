# 🔧 Makefile responsibility split

## 📅 Date: 2025-12-13

## 🎯 Problem

Previously **Makefile.verilator** handled both Verilator and Spike. That caused confusion:
- The Verilator Makefile was running Spike
- `ENABLE_SPIKE`, `ENABLE_COMPARE` flags were tangled
- Responsibilities were unclear

## ✅ Solution: split responsibilities

Each Makefile is now responsible **only for its own job**:

```
┌─────────────────────────────────────────┐
│ Makefile.verilator                     │
│ └─ Verilator only                      │
│    ├─ Build (verilate)                  │
│    ├─ Run RTL simulation               │
│    └─ Open waveforms                   │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│ Makefile.spike                         │
│ └─ Spike only                          │
│    ├─ Run Spike                        │
│    ├─ Compare logs                     │
│    └─ Validate                         │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│ test_manager.py                        │
│ └─ Orchestration                       │
│    ├─ Run RTL                          │
│    ├─ Run validation (optional)        │
│    └─ Generate HTML report             │
└─────────────────────────────────────────┘
```

---

## 📁 Makefile.verilator — Verilator only

### Responsibilities:
- ✅ Verilator build (verilate)
- ✅ Run RTL simulation
- ✅ Generate waveforms
- ✅ Save logs

### Removed:
- ❌ `run-spike` target (→ Makefile.spike)
- ❌ `compare-logs` target (→ Makefile.spike)
- ❌ `html-report` target (→ test_manager.py)
- ❌ `ENABLE_SPIKE` flag
- ❌ `ENABLE_COMPARE` flag
- ❌ `ENABLE_HTML_REPORT` flag

### Usage:

**RTL simulation only (no validation):**
```bash
make -f Makefile.verilator run TEST_NAME=rv32ui-p-add
```

**Result:**
- `results/logs/verilator/rv32ui-p-add/commit_trace.log`
- `results/logs/verilator/rv32ui-p-add/waveform.fst`
- `results/logs/verilator/rv32ui-p-add/uart_output.log`
- **Spike does not run** ✅

---

## 📁 Makefile.spike — Spike only

### Responsibilities:
- ✅ Run Spike
- ✅ Compare RTL and Spike logs
- ✅ Produce diff.log

### Targets:
- `run-spike` — run Spike golden reference
- `compare` — RTL vs Spike comparison
- `validate` — Spike + compare (one command)

### Usage:

**Run Spike:**
```bash
make -f Makefile.spike run-spike \
    TEST_NAME=rv32ui-p-add \
    LOG_DIR=results/logs/verilator/rv32ui-p-add
```

**Compare logs:**
```bash
make -f Makefile.spike compare \
    TEST_NAME=rv32ui-p-add \
    RTL_LOG=results/logs/verilator/rv32ui-p-add/commit_trace.log \
    SPIKE_LOG=results/logs/verilator/rv32ui-p-add/spike_commit.log
```

**Full validation (Spike + compare):**
```bash
make -f Makefile.spike validate \
    TEST_NAME=rv32ui-p-add \
    LOG_DIR=results/logs/verilator/rv32ui-p-add \
    RTL_LOG=results/logs/verilator/rv32ui-p-add/commit_trace.log
```

**Result:**
- `results/logs/verilator/rv32ui-p-add/spike_commit.log`
- `results/logs/verilator/rv32ui-p-add/diff.log`

---

## 🐍 test_manager.py — orchestration

### Responsibilities:
- ✅ Invoke RTL simulation (Makefile.verilator)
- ✅ Invoke validation (validation_runner.py → Makefile.spike)
- ✅ Generate HTML report
- ✅ Test pass/fail decision

### Usage:

**Test with automatic validation:**
```bash
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add
```

**What it does:**
1. `make -f Makefile.verilator run TEST_NAME=rv32ui-p-add` (RTL)
2. `validation_runner.py --test-name rv32ui-p-add` (Spike + compare)
3. Generate HTML report
4. Final result: `TEST PASSED - VALIDATED` or `TEST FAILED`

---

## 🔄 Workflow examples

### Scenario 1: RTL simulation only (quick test)

```bash
# Verilator only, no validation
make -f Makefile.verilator run TEST_NAME=rv32ui-p-add
```

**When to use:**
- Quick RTL change checks
- Inspecting waveforms
- Checking for crashes

---

### Scenario 2: RTL + validation (full test)

```bash
# Automatic validation via test_manager.py
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add
```

**What happens:**
1. RTL simulation runs
2. Spike runs automatically
3. Logs are compared
4. HTML report is generated
5. Result: PASSED/FAILED

**When to use:**
- Regression testing
- Ensuring test correctness
- CI/CD pipelines

---

### Scenario 3: Manual step by step

```bash
# 1. RTL simulation
make -f Makefile.verilator run TEST_NAME=rv32ui-p-add

# 2. Run Spike
make -f Makefile.spike run-spike \
    TEST_NAME=rv32ui-p-add \
    LOG_DIR=results/logs/verilator/rv32ui-p-add

# 3. Compare
make -f Makefile.spike compare \
    TEST_NAME=rv32ui-p-add \
    RTL_LOG=results/logs/verilator/rv32ui-p-add/commit_trace.log \
    SPIKE_LOG=results/logs/verilator/rv32ui-p-add/spike_commit.log
```

**When to use:**
- Debugging
- Customizing Spike parameters
- Step-by-step control

---

## 🎯 Benefits

### ✅ Clear split
- Verilator Makefile → Verilator only
- Spike Makefile → Spike only
- test_manager.py → orchestration

### ✅ Independence
- Makefiles are independent of each other
- Run what you need
- Less confusion

### ✅ Flexibility
- RTL only → quick test
- RTL + validation → full test
- Manual steps → debug

### ✅ Easier maintenance
- Each Makefile owns one area
- Changes are localized
- Structure is easy to follow

---

## 📚 Command cheat sheet

| Goal | Command |
|------|---------|
| **RTL only** | `make -f Makefile.verilator run TEST_NAME=...` |
| **RTL + validation** | `make -f Makefile.verilator test-run TEST_NAME=...` |
| **Spike only** | `make -f Makefile.spike run-spike TEST_NAME=... LOG_DIR=...` |
| **Spike + compare** | `make -f Makefile.spike validate TEST_NAME=... LOG_DIR=... RTL_LOG=...` |
| **Open waveform** | `make -f Makefile.verilator view TEST_NAME=...` |

---

## 🔧 Migration guide

### Old command → new command

```bash
# OLD (no longer works):
make -f Makefile.verilator run TEST_NAME=rv32ui-p-add \
    ENABLE_SPIKE=1 ENABLE_COMPARE=1 ENABLE_HTML_REPORT=1

# NEW:
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add
```

```bash
# OLD (removed):
make -f Makefile.verilator run-spike TEST_NAME=rv32ui-p-add

# NEW:
make -f Makefile.spike run-spike \
    TEST_NAME=rv32ui-p-add \
    LOG_DIR=results/logs/verilator/rv32ui-p-add
```

```bash
# OLD (removed):
make -f Makefile.verilator compare-logs TEST_NAME=rv32ui-p-add

# NEW:
make -f Makefile.spike compare \
    TEST_NAME=rv32ui-p-add \
    RTL_LOG=results/logs/verilator/rv32ui-p-add/commit_trace.log \
    SPIKE_LOG=results/logs/verilator/rv32ui-p-add/spike_commit.log
```

---

## ✅ Fixes

### 1. mkdir error
**Problem:** `mkdir: cannot create directory '': No such file or directory`

**Cause:** `VERILATOR_LOG` was empty when `TEST_NAME` was unset

**Fix:**
```makefile
# OLD:
dirs:
	@mkdir -p "$(BUILD_DIR)" "$(OBJ_DIR)" "$(LOG_DIR)" "$(VERILATOR_LOG)"

# NEW:
dirs:
	@mkdir -p "$(BUILD_DIR)" "$(OBJ_DIR)" "$(RESULTS_DIR)/logs"
	@if [ -n "$(TEST_NAME)" ]; then mkdir -p "$(VERILATOR_LOG)"; fi
```

### 2. Mixed responsibilities
**Problem:** Verilator Makefile was also doing Spike work

**Fix:**
- Spike targets removed
- Validation moved to test_manager.py
- Each Makefile does only its own job

---

## 🎉 Conclusion

You now have:
- ✅ Independent Makefiles
- ✅ Clear responsibilities
- ✅ Simpler usage
- ✅ No mkdir error
- ✅ Verilator = Verilator only
- ✅ Spike = Spike only
- ✅ test_manager.py = orchestration

**Clean, modular, and easy to understand** 🚀
