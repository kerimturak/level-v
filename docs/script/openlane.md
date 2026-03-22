# OpenLane ASIC Flow (SKY130)

This document describes the flow added to take the Level RV32IMC design through open-source physical implementation (PnR) to GDS using public tools.

## Goals

- RTL: `level_wrapper`
- Flow: OpenLane (Yosys + OpenROAD + Magic + Netgen)
- PDK: SKY130 (`sky130A`)

## Commands Added

From the repository root:

```bash
make asic_subrepos
make asic_setup
make asic_prep
make asic_run
make asic_report
make asic_clean
```

The `asic_subrepos` target fetches the following repositories under `subrepo/asic-tools/`:

- `OpenLane`
- `OpenROAD`
- `OpenROAD-flow-scripts`
- `caravel_user_project`
- `caravel`

## Environment Variables

When needed:

```bash
export OPENLANE_IMAGE=efabless/openlane:2023.09.07
export PDK_ROOT=$HOME/.volare
export PDK=sky130A
export TAG=my_run_tag
export OPENLANE_MODE=auto
```

`OPENLANE_MODE` values:

- `auto`: Try Docker if available, otherwise local OpenLane (`subrepo/asic-tools/OpenLane`)
- `docker`: Docker only
- `local`: Local OpenLane only

## Flow Steps

1. `asic_setup`
   - Checks Docker access
   - Pulls the OpenLane image
   - Verifies `PDK_ROOT/PDK` exists

2. `asic_prep`
   - Collects sources from `rtl/` for OpenLane
   - Excludes FPGA/Vivado-oriented files (`xilinx_gpio_wrapper.sv`, `systessis_wrapper.sv`)
   - Copies into `asic/openlane/designs/level_wrapper/src`
   - If Docker is available, generates `level_wrapper_sv2v.v` with `davidsiaw/sv2v` (workaround for Yosys package/import parser limits)

3. `asic_run`
   - Runs the full flow with `flow.tcl`
   - Writes results under `results/asic/openlane/level_wrapper/runs/<tag>`

4. `asic_report`
   - Shows key outputs from the latest run:
     - `metrics.csv`
     - final GDS
     - final DEF
     - final gate-level netlist

## Docker (recommended)

On Ubuntu 22.04:

```bash
chmod +x script/shell/setup_docker_engine_ubuntu.sh
sudo bash script/shell/setup_docker_engine_ubuntu.sh
newgrp docker
docker run --rm hello-world
```

Then run OpenLane in Docker mode:

```bash
OPENLANE_MODE=docker make asic_setup
OPENLANE_MODE=docker make asic_run
```

## Design Configuration

Main files:

- `asic/openlane/designs/level_wrapper/config.tcl`
- `asic/openlane/designs/level_wrapper/constraint.sdc`
- `asic/openlane/designs/level_wrapper/pin_order.cfg`

Initial clock definition:

- `clk_i`
- `20 ns` (`50 MHz`)

Default synthesis defines for a first GDS pass:

- `SYNTHESIS`
- `MINIMAL_SOC`

This starts cache/branch predictor in a smaller configuration; the first goal is to complete the flow end-to-end.

## Important Notes

- For tapeout, aim for **0 DRC** violations and **0 LVS mismatches**.
- On early runs, inspect `asic_report` output and tune `FP_CORE_UTIL`, `PL_TARGET_DENSITY`, and `CLOCK_PERIOD` iteratively.
- For safer tapeout, add post-layout gate-level simulation and SDF validation.
