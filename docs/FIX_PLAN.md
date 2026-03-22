# 🔧 Test system fix plan

## 🎯 Issues found

### 1. ❌ Wrong log directory
**Problem:** Logs should be under `results/logs/verilator/TEST`, not `build/log/verilator/TEST`

**Fix:**
- Makefile.verilator: change `LOG_DIR` variable
- test_manager.py: fix log paths
- validation_runner.py: use `results/`

---

### 2. ❌ Validation not invoked automatically
**Problem:** `test-run` only runs RTL; no Spike validation

**Fix:**
```python
# Inside test_manager.py
def run_test_with_validation(test_name):
    # 1. RTL simulation
    rtl_ok = run_rtl_simulation(test_name)

    if not rtl_ok:
        return "SIMULATION_CRASHED"

    # 2. Validation (optional — per suite)
    if should_validate(test_name):
        validation = run_validation(test_name)
        return "VALIDATED_PASS" if validation.passed else "VALIDATED_FAIL"
    else:
        return "SIMULATION_COMPLETED"
```

---

### 3. ❌ Misleading messages
**Problem:**
- "✓ Test PASSED" → Wrong! Simulation merely finished
- "✓ Simulation successful" → OK when there is no validation

**Fix:**
```python
# verilator_runner.py
if exit_code == 0:
    print("✓ SIMULATION COMPLETED")  # Not "test passed" — simulation
```

```python
# test_manager.py
if simulation_ok and validation_ok:
    print("✅ TEST PASSED - VALIDATED")
elif simulation_ok:
    print("✓ SIMULATION COMPLETED (validation skipped)")
else:
    print("❌ SIMULATION CRASHED")
```

---

### 4. ❌ Simulation duration shows 0.0
**Problem:** Wrong timing calculation in verilator_runner.py

**Fix:**
```python
start_time = datetime.now()
# ... simulation ...
end_time = datetime.now()
elapsed = (end_time - start_time).total_seconds()
print(f"Duration: {elapsed:.2f} s")  # .2f format
```

---

### 5. ❌ Debug log directories empty
**Problem:** Debug logger not writing files

**Fix:**
- debug_logger.py: check file write errors
- Add permission checks
- Ensure directory creation is reliable

---

### 6. ❌ Verilator logs on screen
**Problem:** Verilator output floods the terminal; hard to see summaries

**Fix:**
```python
# verilator_runner.py
LOG_FILE = log_dir / "verilator_full.log"

with open(LOG_FILE, 'w') as logf:
    process = subprocess.run(
        cmd,
        stdout=logf,
        stderr=subprocess.STDOUT
    )

# Show summary only
print("✓ Simulation completed - Full log: {LOG_FILE}")
```

---

### 7. ❌ No HTML report
**Problem:** HTML report not generated automatically

**Fix:**
```python
# test_manager.py
if validation.passed:
    generate_html_report(test_name, validation)
```

---

### 8. ❌ No parameters in debug logs
**Problem:** Unknown which commands ran with which args

**Fix:**
```python
# debug_logger.py — inside step
step.command("verilator --cc ...")
step.arguments(["--test", "rv32ui-p-add", "--max-cycles", "100000"])

# In JSON:
{
  "execution_flow": [
    {
      "command": "verilator --cc ...",
      "args": ["--test", "rv32ui-p-add"],
      "env": {"MAX_CYCLES": "100000"}
    }
  ]
}
```

---

## 🔨 Implementation order

### Phase 1: Log directory layout (critical)
1. Makefile.verilator: `LOG_DIR` → `results/logs/verilator/`
2. test_manager.py: path updates
3. validation_runner.py: path updates

### Phase 2: Message fixes (easy)
1. verilator_runner.py: "Test PASSED" → "SIMULATION COMPLETED"
2. test_manager.py: final decision logic

### Phase 3: Validation integration (medium)
1. test_manager.py: `run_validation()` function
2. test_registry.json: `validation_enabled` flag
3. Automatic invocation

### Phase 4: Debug improvements (easy)
1. Timing fix
2. Command logging
3. Output redirection

### Phase 5: HTML report (optional)
1. Integrate html_report_generator.py

---

## 📝 Priority fixes

### PRIORITY 1: Log directory
**Impact:** High — files were landing in the wrong place

```makefile
# Makefile.verilator
-LOG_DIR := $(BUILD_DIR)/log/verilator/$(TEST_NAME)
+LOG_DIR := $(RESULTS_DIR)/logs/verilator/$(TEST_NAME)
```

### PRIORITY 2: Validation invocation
**Impact:** Critical — test correctness was unknown

```python
# test_manager.py — inside cmd_run()
results = runner.run_tests_with_validation(tests_to_run, **kwargs)
```

### PRIORITY 3: Messages
**Impact:** Medium — user confusion

```python
print("✓ SIMULATION COMPLETED")  # not "Test PASSED"
```

---

## 🧪 Test plan

After each fix:
```bash
# Run test
make -f Makefile.verilator test-run TEST_NAME=rv32ui-p-add

# Verify
ls -la results/logs/verilator/rv32ui-p-add/
cat results/logs/verilator/rv32ui-p-add/diff.log
```

---

## ✅ Success criteria

The fix is successful if:
- ✅ Logs under `results/logs/SIMULATOR/TEST/`
- ✅ Validation runs automatically
- ✅ Correct messages: "SIMULATION COMPLETED" vs "TEST PASSED (VALIDATED)"
- ✅ Duration displayed correctly
- ✅ Debug logs populated and informative
- ✅ Verilator output in file, summary on screen
- ✅ HTML report automatic
- ✅ No permission errors
