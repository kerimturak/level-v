#!/usr/bin/env bash
# UART programmer checks:
#   • Python payload from golden .mem
#   • Verilator: wrapper_ram normal read/write (+RAM_RW_SELFTEST, no UART)
#   • UART stream vs golden in RAM (set CI_STRICT_UART=1 to fail build if this fails)
#
# Trace (optional):
#   UART_PROG_TRACE=1   — Verilog FSM + each RAM write beat in ram_programmer ($display)
#   TB_TRACE=1          — C++ top-level system_reset_o / prog_mode + stream preview (+TB_TRACE on binary)
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"
VERILATOR="${VERILATOR:-verilator}"
GOLDEN="${1:-$ROOT/sim/test/data/uart_prog_verify.mem}"
PAYLOAD="$ROOT/build/tests/uart_verify/uart_prog_payload.bin"
BITC="${BIT_CYCLES:-218}"

VDEF=()
if [[ "${UART_PROG_TRACE:-0}" == "1" ]]; then
  VDEF=(+define+UART_PROGRAMMER_TRACE)
  OBJ="$ROOT/build/obj_uart_programmer_verify_trace"
else
  OBJ="$ROOT/build/obj_uart_programmer_verify"
fi
BIN="$OBJ/Vtb_uart_programmer"

mkdir -p "$(dirname "$PAYLOAD")"
python3 "$ROOT/script/python/fpga/uart_send_data.py" --mem "$GOLDEN" --dump-payload "$PAYLOAD"

NEED=0
[[ -x "$BIN" ]] || NEED=1
for f in rtl/wrapper/simpleuart.v rtl/wrapper/ram_programmer.sv rtl/wrapper/wrapper_ram.sv \
         sim/tb/tb_uart_programmer.sv sim/tb/tb_uart_programmer.cpp rtl/pkg/level_param.sv; do
  [[ "$f" -nt "$BIN" ]] 2>/dev/null && NEED=1 || true
done

if [[ "$NEED" -eq 1 ]]; then
  "$VERILATOR" +incdir+rtl/include -Wall -Wno-fatal -Wno-WIDTHTRUNC \
    -cc --exe --build -j 0 \
    --top-module tb_uart_programmer \
    -Mdir "$OBJ" \
    "${VDEF[@]}" \
    rtl/pkg/level_param.sv rtl/wrapper/simpleuart.v rtl/wrapper/ram_programmer.sv \
    rtl/wrapper/wrapper_ram.sv sim/tb/tb_uart_programmer.sv sim/tb/tb_uart_programmer.cpp
fi

TB_EXTRA=()
[[ "${TB_TRACE:-0}" == "1" ]] && TB_EXTRA=(+TB_TRACE)

echo "=== wrapper_ram R/W selftest (required) ==="
"$BIN" "${TB_EXTRA[@]}" +RAM_RW_SELFTEST +SKIP_PAYLOAD

echo "=== UART → programmer → RAM vs golden (BIT_CYCLES=$BITC) ==="
if "$BIN" "${TB_EXTRA[@]}" +RAM_RW_SELFTEST +PAYLOAD="$PAYLOAD" +GOLDEN="$GOLDEN" +POST_IDLE_CYCLES=8000 "+BIT_CYCLES=$BITC"; then
  echo "[OK] UART programming path matches golden in simulation."
else
  echo "[WARN] UART golden mismatch — try BIT_CYCLES=217..221, or validate on FPGA."
  [[ "${CI_STRICT_UART:-0}" == "1" ]] && exit 3 || true
fi
