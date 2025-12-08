#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
VERILATOR=${VERILATOR:-verilator}

echo "Running PMA test via Verilator"
cd "$ROOT"

${VERILATOR} -sv --cc \
  sim/tb/pma_tb.sv \
  rtl/core/pmp_pma/pma.sv \
  rtl/pkg/ceres_param.sv \
  -Irtl/include \
  --exe sim/tb/main.cpp

make -C obj_dir -j -f Vpma_tb.mk Vpma_tb

./obj_dir/Vpma_tb
