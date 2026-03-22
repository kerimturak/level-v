# CoreMark (Level-V / Verilator)

CoreMark is built with the in-tree **levelv** port (`env/coremark/levelv/`) and run on the RTL simulation.

## Build

```bash
make coremark
```

Artifacts under `build/tests/coremark/` (e.g. `coremark.mem` for simulation).

## Run

```bash
make run_coremark
```

Optional: `COREMARK_ITERATIONS`, `MAX_CYCLES`, `FAST_SIM=1`, `MINIMAL_SOC=1` — see `make coremark_help`.

Logs: `results/logs/<SIM>/coremark/` (e.g. `uart_output.log`).

## Clean

```bash
make coremark_clean
```

Removes Level build outputs and any leftover `subrepo/coremark/spike-pk` copy from older flows.
