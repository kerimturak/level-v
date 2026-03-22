# 🔍 Level RISC-V Validation System

## 📋 Overview

We split the test validation system into **3 layers**:

```
┌─────────────────────────────────────────┐
│ Layer 1: RTL Simulation                │
│ ├─ verilator_runner.py                 │
│ └─ Result: SIMULATION_COMPLETED/CRASHED │
└─────────────────────────────────────────┘
              ↓
┌─────────────────────────────────────────┐
│ Layer 2: Validation                    │
│ ├─ Makefile.spike (run Spike)          │
│ ├─ validation_runner.py (orchestrator) │
│ └─ Result: VALIDATED_PASS/FAIL         │
└─────────────────────────────────────────┘
              ↓
┌─────────────────────────────────────────┐
│ Layer 3: Test Management               │
│ ├─ test_manager.py (coordination)      │
│ └─ Final: PASS/FAIL + debug report     │
└─────────────────────────────────────────┘
```

---

## 🎯 Separation of responsibilities

### 1️⃣ **RTL simulation** (`verilator_runner.py`)

**Responsibility:** Run simulation only  
**Success criterion:** Finish without crashing

```python
# verilator_runner.py
if exit_code == 0:
    print("✓ Simulation successful")  # ← Correct: no crash
    return 0
else:
    print("✗ Simulation crashed")
    return 1
```

**Result messages:**
- ✅ `SIMULATION_COMPLETED` — simulation finished without crashing
- ❌ `SIMULATION_CRASHED` — simulation crashed

**IMPORTANT:** This layer must **NOT** decide **test pass/fail**!

---

### 2️⃣ **Validation** (`Makefile.spike` + `validation_runner.py`)

**Responsibility:** Compare RTL output with Spike  
**Success criterion:** RTL commit log == Spike commit log

```bash
# Makefile.spike usage
make -f Makefile.spike run-spike \
    TEST_NAME=rv32ui-p-add \
    LOG_DIR=build/log/verilator/rv32ui-p-add

make -f Makefile.spike compare \
    TEST_NAME=rv32ui-p-add \
    RTL_LOG=build/log/.../commit_trace.log \
    SPIKE_LOG=build/log/.../spike_commit.log
```

```python
# validation_runner.py usage
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-add \
    --log-dir build/log/verilator/rv32ui-p-add

# Result:
{
  "status": "VALIDATED_PASS",
  "rtl_instructions": 2900,
  "spike_instructions": 2900,
  "matched_instructions": 2900,
  "match_percentage": 100.0
}
```

**Result states:**
- ✅ `VALIDATED_PASS` — logs match exactly
- ❌ `VALIDATED_FAIL` — logs differ
- ⚠️ `SPIKE_FAILED` — Spike could not be run
- ⚠️ `RTL_LOG_MISSING` — no RTL log
- ⚠️ `SPIKE_SKIPPED` — validation skipped

---

### 3️⃣ **Test manager** (`test_manager.py`)

**Responsibility:** Coordinate the full pipeline  
**Final decision:** Pass/fail + debug report

```python
# test_manager.py workflow
1. Run RTL simulation → verilator_runner.py
2. If simulation_completed:
     a. Run validation → validation_runner.py
     b. PASS/FAIL based on validation result
3. Build debug report
4. Report result to the user
```

**Final outcomes:**
- ✅ `TEST_PASSED` — simulation + validation succeeded
- ❌ `TEST_FAILED` — validation failed (logs did not match)
- ❌ `SIMULATION_CRASHED` — simulation crashed
- ⚠️ `VALIDATION_SKIPPED` — validation not run (benchmark mode)

---

## 📁 New files

### 1. `Makefile.spike`
**Standalone Spike Makefile**

Features:
- Run Spike standalone
- Compare logs
- Auto-detect test type
- Minimal dependencies

Usage:
```bash
# Run Spike
make -f Makefile.spike run-spike TEST_NAME=rv32ui-p-add LOG_DIR=build/log/test

# Compare logs
make -f Makefile.spike compare \
    TEST_NAME=rv32ui-p-add \
    RTL_LOG=build/log/test/commit_trace.log \
    SPIKE_LOG=build/log/test/spike_commit.log

# Full validation
make -f Makefile.spike validate \
    TEST_NAME=rv32ui-p-add \
    BUILD_DIR=build \
    LOG_DIR=build/log/test \
    RTL_LOG=build/log/test/commit_trace.log
```

### 2. `script/python/validation_runner.py`
**Validation orchestration tool**

Features:
- Spike + compare in one command
- Metrics extraction
- JSON output
- Error handling

Usage:
```bash
# Simple usage
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-add \
    --log-dir build/log/verilator/rv32ui-p-add

# Skip Spike (compare only)
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-add \
    --log-dir build/log/verilator/rv32ui-p-add \
    --skip-spike

# JSON output
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-add \
    --log-dir build/log/verilator/rv32ui-p-add \
    --json-output validation_result.json
```

---

## 🔄 Full workflow

### Scenario 1: Full validation

```bash
# 1. RTL simulation
make -f Makefile.verilator run TEST_NAME=rv32ui-p-add
# → Result: build/log/verilator/rv32ui-p-add/commit_trace.log

# 2. Validation
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-add \
    --log-dir build/log/verilator/rv32ui-p-add
# → Spike runs, logs are compared

# 3. Outcome
# ✅ VALIDATED_PASS — test passed
# ❌ VALIDATED_FAIL — test failed
```

### Scenario 2: Benchmark (no validation)

```bash
# Benchmark tests skip validation
make -f Makefile.verilator test-run TEST_NAME=coremark
# → Simulation only
# → Result: SIMULATION_COMPLETED (no validation)
```

### Scenario 3: Manual validation

```bash
# RTL first
make -f Makefile.verilator run TEST_NAME=rv32ui-p-add

# Then Spike (separate)
make -f Makefile.spike run-spike \
    TEST_NAME=rv32ui-p-add \
    LOG_DIR=build/log/verilator/rv32ui-p-add

# Then compare (separate)
make -f Makefile.spike compare \
    TEST_NAME=rv32ui-p-add \
    RTL_LOG=build/log/verilator/rv32ui-p-add/commit_trace.log \
    SPIKE_LOG=build/log/verilator/rv32ui-p-add/spike_commit.log
```

---

## 📊 Validation result format

### JSON output

```json
{
  "test_name": "rv32ui-p-add",
  "status": "VALIDATED_PASS",
  "passed": true,
  "rtl_log_exists": true,
  "spike": {
    "ran": true,
    "success": true
  },
  "comparison": {
    "ran": true,
    "logs_match": true
  },
  "metrics": {
    "rtl_instructions": 2900,
    "spike_instructions": 2900,
    "matched_instructions": 2900,
    "first_mismatch_line": null,
    "match_percentage": 100.0
  },
  "errors": [],
  "warnings": []
}
```

### Failed test example

```json
{
  "test_name": "rv32ui-p-buggy",
  "status": "VALIDATED_FAIL",
  "passed": false,
  "metrics": {
    "rtl_instructions": 2900,
    "spike_instructions": 2900,
    "matched_instructions": 2850,
    "first_mismatch_line": 2851,
    "match_percentage": 98.3
  },
  "errors": [],
  "warnings": ["First mismatch at line 2851"]
}
```

---

## 🎯 Benefits

### ✅ Separation of concerns
- Each layer does one job
- RTL simulation is independent of validation
- Validation is independent of RTL

### ✅ Modular structure
- You can run Spike standalone
- You can re-run validation
- Usable without the test manager

### ✅ Debug-friendly
- Each step produces its own logs
- JSON outputs are easy to parse
- Easier troubleshooting

### ✅ Backward compatible
- Legacy `make run` still works
- Existing test workflows preserved
- New features are optional

---

## 🔧 Future improvements

### 1. Test manager integration
```python
# In test_manager.py
def run_test_with_validation(test_name):
    # 1. RTL simulation
    rtl_result = run_rtl_simulation(test_name)

    # 2. If simulation succeeded
    if rtl_result.status == "COMPLETED":
        # 3. Run validation
        validation = run_validation(test_name)

        # 4. Final decision
        if validation.passed:
            return "TEST_PASSED"
        else:
            return "TEST_FAILED"
    else:
        return "SIMULATION_CRASHED"
```

### 2. Richer debug report
```json
{
  "result": {
    "simulation": "COMPLETED",  # RTL simulation status
    "validation": "FAILED",     # Validation status
    "final_status": "FAILED"    # Final decision
  },
  "validation_details": {
    "rtl_instructions": 2900,
    "spike_instructions": 2900,
    "match_percentage": 98.3,
    "first_mismatch": {
      "line": 2851,
      "rtl_pc": "0x80001234",
      "spike_pc": "0x80001238"
    }
  }
}
```

### 3. Auto-enable validation
```json
// test_registry.json
{
  "test_suites": {
    "isa_basic": {
      "validation": {
        "enabled": true,
        "spike_isa": "rv32imc_zicsr"
      }
    },
    "benchmarks": {
      "validation": {
        "enabled": false  // No validation for benchmarks
      }
    }
  }
}
```

---

## 📞 Usage examples

### Example 1: Quick test + validation

```bash
# Run test (RTL only)
make -f Makefile.verilator run TEST_NAME=rv32ui-p-add

# Add validation
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-add \
    --log-dir build/log/verilator/rv32ui-p-add
```

### Example 2: Validation only (RTL already ran)

```bash
# RTL already ran; run validation only
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-add \
    --log-dir build/log/verilator/rv32ui-p-add
```

### Example 3: Customize Spike parameters

```bash
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-custom \
    --log-dir build/log/verilator/rv32ui-p-custom \
    --spike-isa rv32im_zicsr \
    --spike-pc 0x80000000
```

### Example 4: Resync mode (consume differences)

```bash
python3 script/python/validation_runner.py \
    --test-name rv32ui-p-add \
    --log-dir build/log/verilator/rv32ui-p-add \
    --resync
```

---

## ✅ Summary

| Layer | Responsibility | Success criterion | Output |
|--------|----------------|-------------------|--------|
| **RTL sim** | Run simulation | No crash | `COMPLETED`/`CRASHED` |
| **Validation** | Spike + compare | RTL == Spike | `VALIDATED_PASS`/`FAIL` |
| **Test manager** | Orchestrate + decide | Full pipeline | `TEST_PASSED`/`FAILED` |

**Golden rule:** Each layer decides only within its own responsibility!

---

## 🎉 Conclusion

You now have:
- ✅ RTL simulation separate from validation
- ✅ Spike can run standalone
- ✅ Validation can be re-run
- ✅ Clear test pass/fail criteria
- ✅ Debug-friendly structure
- ✅ Modular and extensible

**Test results are now meaningful:**
- Simulation ran ≠ test passed
- RTL == Spike → test passed ✅
