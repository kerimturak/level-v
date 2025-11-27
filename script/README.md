# Scripts
All automation, tooling, and helper scripts for the project.

## Quick Start

This quick section shows the most common commands to build and run simulations and to use the Python helpers.

1. Create a Python virtual environment and install Python dependencies:

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r script/requirements.txt
```

2. Build Verilated C++ model (from repository root):

```bash
make verilate
```

3. Run a single test using the wrapper (resolves MEM file automatically):

```bash
make run_verilator TEST_NAME=rv32ui-p-add MAX_CYCLES=100000
```

4. Or call the wrapper directly (useful in CI/debug):

```bash
VERILATOR_LOG_DIR=results/logs/verilator/rv32ui-p-add \\
TEST_NAME=rv32ui-p-add MAX_CYCLES=100000 ./script/run_verilator.sh
```

5. Full pipeline (RTL + Spike + compare):

```bash
make run TEST_NAME=rv32ui-p-add
```

Troubleshooting

- If you see `Simulation binary not found`, run `make verilate` first (builds `$(OBJ_DIR)/V$(RTL_LEVEL)`).
- If Verilator reports missing includes (e.g. `ceres_defines.svh`), ensure `INC_DIR` and include files are present and `make verilate` is invoked from the repo root so include paths resolve.
- Check logs under `results/logs/verilator/<TEST_NAME>/`:
	- `verilator_run.log` — console output of the simulation run
	- `commit_trace.log` — commit trace used by `compare_logs.py`
	- `ceres.log` — tracer pipeline log
	- `summary.json` — short machine-readable run summary (added by `run_verilator.sh`)

If you'd like, I can add a short GitHub Actions workflow to run `make verilator_static` and basic Python checks on PRs.

Running tests

After creating a virtual environment and installing dev requirements run:

```bash
source .venv/bin/activate
pip install -r script/requirements-dev.txt
pytest -q
```
