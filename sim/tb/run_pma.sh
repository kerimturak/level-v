#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
VERILATOR=${VERILATOR:-verilator}

echo "Running PMA test via Verilator"
cd "$ROOT"

mkdir -p build/gen
python3 script/python/gen_level_param_profile.py full_soc --out build/gen/level_param_profile.svh

${VERILATOR} -sv --cc \
  sim/tb/pma_tb.sv \
  rtl/core/pmp_pma/pma.sv \
  rtl/pkg/level_param.sv \
  -Irtl/include \
  -Ibuild/gen \
  --exe sim/tb/main.cpp

make -C obj_dir -j -f Vpma_tb.mk Vpma_tb

./obj_dir/Vpma_tb
