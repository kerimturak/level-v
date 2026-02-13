Harika Kerim 💪
Şimdi aşağıda sana `rules_verilator.mk` dosyası için profesyonel düzeyde bir **dokümantasyon** hazırladım.
Bu dokümantasyon hem proje ekibine hem de senin ileride GitHub repo’na koymak istediğin teknik referans olarak uygundur.
Format olarak Markdown (.md) şeklinde düzenledim, Hugo, GitHub Wiki veya internal doc için direkt kullanılabilir.

---

# 🧩 **Verilator Makefile Documentation**

> **File:** `script/makefiles/rules_verilator.mk`
> **Purpose:** Automate linting, building, simulating, profiling, and analyzing SystemVerilog designs using **Verilator**.

---

## 🧱 Overview

This Makefile module provides a **modular, automated simulation infrastructure** for Verilator-based verification flows.

It is designed for:

* RISC-V or custom CPU cores
* ASIC/FPGA simulation environments
* Continuous integration (CI/CD) flows
* Research or teaching setups

### 🔥 Features

* ✅ Automatic lint, loop, and static checks
* ✅ C++ model build & run with Verilator
* ✅ Coverage & performance profiling support
* ✅ JSON AST and formal preparation modes
* ✅ Colorized terminal output
* ✅ GTKWave auto-launch (with `GUI=1`)
* ✅ Works with Verilator **4.x and 5.x**
* ✅ Portable across **Linux / WSL / MSYS2**

---

## ⚙️ Configuration Variables

| Variable    | Default         | Description                                                 |
| ----------- | --------------- | ----------------------------------------------------------- |
| `TRACE`     | `0`             | Enables waveform tracing (VCD/FST).                         |
| `VERBOSE`   | `0`             | Enables full Verilator log output.                          |
| `GUI`       | `0`             | Automatically launches GTKWave after simulation.            |
| `INC_DIR`   | *(from parent)* | Include directory for RTL headers.                          |
| `OBJ_DIR`   | *(from parent)* | Directory for Verilator build outputs.                      |
| `LOG_DIR`   | *(from parent)* | Directory for log files.                                    |
| `TOP_LEVEL` | *(from parent)* | Name of top-level SystemVerilog module (e.g. `tb_wrapper`). |
| `SIM_DIR`   | *(from parent)* | Simulation directory (contains `verilator_main.cpp`).       |
| `OPT_LEVEL` | `-O0`           | Optimization level for C++ compilation.                     |

> These variables are inherited from your **main Makefile** (e.g. `config.mk`).

---

## 🧮 Major Targets

### 1️⃣ `make lint`

Performs Verilator lint and combinational loop checks.

**Command:**

```bash
make lint
```

**What it does:**

* Runs `verilator --lint-only` on all sources.
* Checks for unconnected signals, combinational loops, and syntax issues.
* Saves output to `build/logs/verilator_lint.log`.

**Output Example:**

```
[VERILATOR LINT & LOOP CHECK — Debug]
✅ No combinational loops found.
```

---

### 2️⃣ `make verilate`

Generates a **C++ simulation model** of the SystemVerilog design.

**Command:**

```bash
make verilate TRACE=1 VERBOSE=0
```

**Options:**

| Option      | Description                            |
| ----------- | -------------------------------------- |
| `TRACE=1`   | Enables VCD/FST waveform dump support. |
| `VERBOSE=1` | Shows detailed Verilator logs.         |

**Behavior:**

* Runs `verilator -cc` to build C++ model.
* Links it with `verilator_main.cpp`.
* Generates binary: `build/obj_dir/Vtb_wrapper`.

**Output Files:**

* `build/obj_dir/` → Generated `.cpp`, `.o`, `.mk`, and final binary.
* `build/logs/verilator_build.log` → Detailed build log.

---

### 3️⃣ `make run_verilator`

Runs the compiled Verilator model.

**Command:**

```bash
make run_verilator GUI=1
```

**Options:**

| Option  | Description                                  |
| ------- | -------------------------------------------- |
| `GUI=1` | Launches GTKWave if `dump.vcd` is generated. |

**Behavior:**

* Executes the binary `obj_dir/Vtb_wrapper`.
* Logs output to `verilator_run.log`.
* Optionally opens GTKWave.

**Example Output:**

```
[RUNNING VERILATOR SIMULATION]
✅ Verilator simulation complete.
🌈 Opening waveform in GTKWave...
```

---

### 4️⃣ `make verilator_static`

Performs deep structural checks (no simulation).

**Purpose:**
Detects unconnected nets, unused variables, multiple drivers, or unoptimized signals.

**Log file:**
`build/logs/verilator_static.log`

---

### 5️⃣ `make verilator_coverage` & `make run_coverage`

Enables **code coverage instrumentation**.

**Steps:**

```bash
make verilator_coverage
make run_coverage
```

**Generates:**

* `cov.dat` — Coverage data file.
* Annotated report using:

  ```
  verilator_coverage --write-info max --annotate obj_dir/Vtb_wrapper --annotate-points cov.dat
  ```

**Use Cases:**

* Statement, toggle, and branch coverage tracking.

---

### 6️⃣ `make verilator_profile`

Builds model with **performance profiling** enabled.

**Purpose:**
Measure execution time of internal simulation functions (C++ level).

**After running:**

```bash
./build/obj_dir/Vtb_wrapper +verilator+prof+exec+file+perf.vlt
verilator_gantt perf.vlt
```

→ Generates an interactive Gantt chart of simulation performance.

---

### 7️⃣ `make verilator_json`

Exports the parsed design as a **JSON AST (Abstract Syntax Tree)**.

**Output:**
`ast_dump.json`

**Use Case:**
Debugging generate blocks, signal hierarchies, or macro expansions.

---

### 8️⃣ `make verilator_formal_prep`

Generates a **timing-free, black-box ready** version of the design for formal verification (e.g. Yosys-SMT, SymbiYosys).

**Flags Used:**

```
--no-timing --bbox-unsup --lint-only
```

---

### 9️⃣ `make clean_verilator`

Cleans all Verilator build artifacts.

**Removes:**

* `obj_dir/`
* Coverage, profiling, JSON files
* All Verilator logs

**Command:**

```bash
make clean_verilator
```

---

### 🔟 `make verilator_clean_logs`

Removes only logs and temporary reports (preserves build outputs).

**Command:**

```bash
make verilator_clean_logs
```

---

## 📁 File & Directory Layout

```
project_root/
├── rtl/                 # RTL source files
├── sim/
│   ├── tb/              # Testbench sources
│   └── cpp/verilator_main.cpp  # Verilator main driver
├── build/
│   ├── obj_dir/         # Generated C++ model + binary
│   └── logs/            # Verilator logs
└── script/
    └── makefiles/
        └── rules_verilator.mk
```

---

## 📊 Generated Artifacts

| File                  | Description                          |
| --------------------- | ------------------------------------ |
| `obj_dir/Vtb_wrapper` | Compiled Verilator simulation binary |
| `dump.vcd`            | Waveform dump (if TRACE=1)           |
| `cov.dat`             | Coverage database                    |
| `perf.vlt`            | Performance Gantt input              |
| `ast_dump.json`       | AST JSON export                      |
| `verilator_*.log`     | Logs (lint, build, run, etc.)        |

---

## 💡 Integration Example (Main Makefile)

Your main project Makefile can simply include:

```makefile
include script/makefiles/rules_verilator.mk
```

And define the environment in `config.mk`:

```makefile
INC_DIR  := ./rtl/include
OBJ_DIR  := ./build/obj_dir
LOG_DIR  := ./build/logs
TOP_LEVEL := tb_wrapper
SIM_DIR  := ./sim
OPT_LEVEL := -O0
```

Then run:

```bash
make verilate TRACE=1
make run_verilator GUI=1
```

---

## 🧠 Best Practices

1. **Use TRACE=1** only when debugging — it slows down the simulation.
2. **Keep obj_dir/** under `.gitignore`. It contains generated C++.
3. For CI/CD, use:

   ```bash
   make lint
   make verilator_static
   make verilate VERBOSE=0
   ```
4. For profiling long simulations, use `verilator_profile` + `verilator_gantt`.
5. For regression reporting, store `cov.dat` in artifacts.

---

## 📘 References

* [Verilator User Guide](https://verilator.org/guide/latest/)
* [Verilator Command Line Options](https://verilator.org/guide/latest/exe_verilator.html)
* [Verilator Gantt Visualization](https://verilator.org/guide/latest/tools.html#verilator-gantt)
* [Verilator Coverage Tool](https://verilator.org/guide/latest/tools.html#verilator-coverage)

---

## 🏁 Summary

| Target                                | Purpose                    |
| ------------------------------------- | -------------------------- |
| `lint`                                | Syntax & loop check        |
| `verilate`                            | Build model                |
| `run_verilator`                       | Run simulation             |
| `verilator_static`                    | Structural design analysis |
| `verilator_coverage` / `run_coverage` | Coverage analysis          |
| `verilator_profile`                   | Performance profiling      |
| `verilator_json`                      | JSON AST export            |
| `verilator_formal_prep`               | Formal verification prep   |
| `clean_verilator`                     | Clean all                  |
| `verilator_clean_logs`                | Clean logs only            |

---

Would you like me to also prepare a **PDF documentation version** (formatted for project sharing or internal wiki, with table of contents and logo header)?
