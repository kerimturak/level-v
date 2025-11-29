#!/usr/bin/env bash
# Lightweight wrapper for running the Verilator simulation binary
# - sets safe shell flags
# - resolves MEM file or TEST_NAME
# - invokes the Verilated binary and writes logs + a small JSON summary
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
BUILD_DIR="${BUILD_DIR:-$ROOT_DIR/build}"
RESULTS_DIR="${RESULTS_DIR:-$ROOT_DIR/results}"
OBJ_DIR="${OBJ_DIR:-$BUILD_DIR/obj_dir}"
RTL_LEVEL="${RTL_LEVEL:-ceres_wrapper}"
RUN_BIN="${RUN_BIN:-$OBJ_DIR/V${RTL_LEVEL}}"

# Inputs (export environment variables or provide on command line)
# EXPECTED env:
#   TEST_NAME, MEM_FILE, MAX_CYCLES, VERILATOR_LOG_DIR
: "${MAX_CYCLES:=100000}"

if [ -z "${VERILATOR_LOG_DIR:-}" ]; then
  if [ -z "${TEST_NAME:-}" ]; then
    echo "[ERROR] Provide TEST_NAME or set VERILATOR_LOG_DIR" >&2
    exit 2
  fi
  VERILATOR_LOG_DIR="$RESULTS_DIR/logs/verilator/$TEST_NAME"
fi

mkdir -p "$VERILATOR_LOG_DIR"

# Resolve MEM_PATH
MEM_PATH=""
if [ -n "${MEM_FILE:-}" ]; then
  if [ "${MEM_FILE}" = "-" ]; then
    MEM_PATH=""
  elif [[ "$MEM_FILE" = /* ]] && [ -f "$MEM_FILE" ]; then
    MEM_PATH="$(realpath "$MEM_FILE")"
  else
    # search build tests mem dirs
    FOUND=""
    for d in "$BUILD_DIR"/tests/*/mem; do
      if [ -f "$d/$MEM_FILE" ]; then
        FOUND="$d/$MEM_FILE"
        break
      fi
    done
    if [ -n "$FOUND" ]; then
      MEM_PATH="$(realpath "$FOUND")"
    else
      echo "[ERROR] MEM_FILE '$MEM_FILE' not found in build tests mem dirs" >&2
      exit 3
    fi
  fi
else
  # search by TEST_NAME
  if [ -n "${TEST_NAME:-}" ]; then
    FOUND=""
    # Search in */mem subdirectories (riscv-tests style)
    for d in "$BUILD_DIR"/tests/*/mem; do
      if [ -f "$d/$TEST_NAME.mem" ]; then FOUND="$d/$TEST_NAME.mem"; break; fi
      if [ -f "$d/$TEST_NAME.hex" ]; then FOUND="$d/$TEST_NAME.hex"; break; fi
    done
    # Also search directly in test directories (coremark style)
    if [ -z "$FOUND" ]; then
      for d in "$BUILD_DIR"/tests/*; do
        if [ -f "$d/$TEST_NAME.mem" ]; then FOUND="$d/$TEST_NAME.mem"; break; fi
        if [ -f "$d/$TEST_NAME.hex" ]; then FOUND="$d/$TEST_NAME.hex"; break; fi
      done
    fi
    if [ -n "$FOUND" ]; then
      MEM_PATH="$(realpath "$FOUND")"
    else
      echo "[ERROR] Could not locate MEM/HEX for TEST_NAME='$TEST_NAME' under $BUILD_DIR/tests/" >&2
      exit 4
    fi
  else
    echo "[ERROR] Either MEM_FILE or TEST_NAME must be provided" >&2
    exit 5
  fi
fi

echo "[INFO] INIT_FILE => ${MEM_PATH:-<none>}"
echo "[INFO] test_name => ${TEST_NAME:-<none>}"
echo "[INFO] log dir   => $VERILATOR_LOG_DIR"
echo "[INFO] MAX_CYCLES => $MAX_CYCLES"

if [ ! -x "$RUN_BIN" ]; then
  echo "[ERROR] Simulation binary not found: $RUN_BIN" >&2
  exit 6
fi

# Optional addr file - skip if NO_ADDR is set
NO_ADDR="${NO_ADDR:-0}"

# Try multiple locations for addr file
ADDR_FILE=""
for addr_dir in "$BUILD_DIR"/tests/*/pass_fail_addr; do
  if [ -f "$addr_dir/${TEST_NAME}_addr.txt" ]; then
    ADDR_FILE="$addr_dir/${TEST_NAME}_addr.txt"
    break
  fi
done

if [ "$NO_ADDR" = "1" ]; then
  echo "[INFO] Address checking disabled (NO_ADDR=1)"
  ADDR_ARG="+no_addr"
elif [ -n "$ADDR_FILE" ] && [ -f "$ADDR_FILE" ]; then
  echo "[INFO] addr_file => $ADDR_FILE"
  ADDR_ARG="+addr_file=$ADDR_FILE"
else
  echo "[INFO] No addr_file found, disabling address check"
  ADDR_ARG="+no_addr"
fi

# Allow callers to pass extra plusargs to the simulation binary (e.g. +define+FETCH_LOGGER)
# Set SIM_PLUSARGS env var to forward arbitrary plusargs.
SIM_PLUSARGS=${SIM_PLUSARGS:-}

# Run binary
"$RUN_BIN" "$MAX_CYCLES" \
  +INIT_FILE="$MEM_PATH" \
  +simulator=verilator \
  +test_name="${TEST_NAME}" \
  +trace_file="${VERILATOR_LOG_DIR}/commit_trace.log" \
  +log_path="${VERILATOR_LOG_DIR}/ceres.log" \
  +uart_log_path="${VERILATOR_LOG_DIR}/uart_output.log" \
  +DUMP_FILE="${VERILATOR_LOG_DIR}/waveform.fst" \
  ${ADDR_ARG} ${SIM_PLUSARGS} | tee "${VERILATOR_LOG_DIR}/verilator_run.log"
EXIT_CODE=${PIPESTATUS[0]:-0}

# Write a brief JSON summary for CI consumption
SUMMARY="${VERILATOR_LOG_DIR}/summary.json"
cat > "$SUMMARY" <<EOF
{
  "test_name": "${TEST_NAME:-}",
  "mem_path": "${MEM_PATH:-}",
  "verilator_log_dir": "${VERILATOR_LOG_DIR}",
  "exit_code": ${EXIT_CODE}
}
EOF

if [ "$EXIT_CODE" -ne 0 ]; then
  echo "[ERROR] Simulation exited with code $EXIT_CODE" >&2
  exit "$EXIT_CODE"
fi

echo "[INFO] Verilator simulation complete. Logs: $VERILATOR_LOG_DIR"
exit 0
