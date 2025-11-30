#!/usr/bin/env bash
# =========================================
# CERES RISC-V — Test Config Parser
# =========================================
# Reads test configuration JSON files and outputs Make-compatible variables
# Supports inheritance via "extends" field
#
# Usage:
#   ./parse_test_config.sh isa                    # Parse isa.json
#   ./parse_test_config.sh isa --make             # Output for Make include
#   ./parse_test_config.sh isa --get simulation.max_cycles  # Get single value
#   ./parse_test_config.sh isa --env              # Export to environment
#   ./parse_test_config.sh --list                 # List available configs
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CONFIG_DIR="${SCRIPT_DIR}/../config/tests"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
RESET='\033[0m'

# -----------------------------------------
# Check for jq
# -----------------------------------------
check_jq() {
  if ! command -v jq &>/dev/null; then
    echo -e "${RED}[ERROR]${RESET} jq is required but not installed." >&2
    echo "Install with: sudo apt install jq" >&2
    exit 1
  fi
}

# -----------------------------------------
# Show usage
# -----------------------------------------
usage() {
  cat <<EOF
CERES RISC-V Test Configuration Parser

Usage: $(basename "$0") <config_name> [options]

Options:
  --make              Output Make-compatible variable assignments
  --env               Output environment variable exports
  --get <path>        Get a single value (e.g., simulation.max_cycles)
  --defines           Output only SV_DEFINES string
  --list              List available configurations
  --help              Show this help

Config Names:
  default, isa, arch, imperas, bench, coremark, csr

Examples:
  $(basename "$0") isa --make           # For Makefile include
  $(basename "$0") bench --defines      # Get SV defines
  $(basename "$0") coremark --get simulation.max_cycles
  $(basename "$0") --list

EOF
}

# -----------------------------------------
# List available configs
# -----------------------------------------
list_configs() {
  echo -e "${CYAN}Available Test Configurations:${RESET}"
  echo ""
  for config in "$CONFIG_DIR"/*.json; do
    if [ -f "$config" ]; then
      name=$(basename "$config" .json)
      if [ "$name" != "tests.schema" ]; then
        desc=$(jq -r '._description // "No description"' "$config" 2>/dev/null)
        printf "  ${GREEN}%-12s${RESET} %s\n" "$name" "$desc"
      fi
    fi
  done
  echo ""
}

# -----------------------------------------
# Load config with inheritance
# -----------------------------------------
load_config() {
  local config_name="$1"
  local config_file="${CONFIG_DIR}/${config_name}.json"
  
  if [ ! -f "$config_file" ]; then
    echo -e "${RED}[ERROR]${RESET} Config not found: $config_file" >&2
    exit 1
  fi
  
  local config
  config=$(cat "$config_file")
  
  # Check for extends field
  local extends
  extends=$(echo "$config" | jq -r '.extends // empty')
  
  if [ -n "$extends" ]; then
    # Load parent config recursively
    local parent_config
    parent_config=$(load_config "$extends")
    
    # Merge parent with current (current overrides parent)
    config=$(echo "$parent_config" "$config" | jq -s '.[0] * .[1]')
  fi
  
  echo "$config"
}

# -----------------------------------------
# Get a single value
# -----------------------------------------
get_value() {
  local config="$1"
  local path="$2"
  
  echo "$config" | jq -r ".$path // empty"
}

# -----------------------------------------
# Generate SV_DEFINES string
# -----------------------------------------
generate_defines() {
  local config="$1"
  
  local defines=""
  
  # Extract all defines that are true
  while IFS= read -r line; do
    defines="$defines $line"
  done < <(echo "$config" | jq -r '
    .defines // {} |
    to_entries |
    map(select(.value == true) | "+define+\(.key)") |
    .[]
  ')
  
  echo "$defines"
}

# -----------------------------------------
# Convert to Make variables
# -----------------------------------------
to_make_vars() {
  local config="$1"
  
  cat <<'MAKEVARS'
# =========================================
# Auto-generated from test config JSON
# Do not edit manually
# =========================================

MAKEVARS

  # Simulation settings
  echo "# Simulation settings"
  local max_cycles
  max_cycles=$(echo "$config" | jq -r '.simulation.max_cycles // 10000')
  echo "CFG_MAX_CYCLES := $max_cycles"
  
  local timeout
  timeout=$(echo "$config" | jq -r '.simulation.timeout_seconds // 60')
  echo "CFG_TIMEOUT := $timeout"
  
  local parallel
  parallel=$(echo "$config" | jq -r '.simulation.parallel_jobs // "auto"')
  if [ "$parallel" = "auto" ]; then
    echo "CFG_PARALLEL_JOBS := \$(shell nproc 2>/dev/null || echo 4)"
  else
    echo "CFG_PARALLEL_JOBS := $parallel"
  fi
  
  echo ""
  
  # Comparison settings
  echo "# Comparison settings"
  local compare_enabled
  compare_enabled=$(echo "$config" | jq -r '.comparison.enabled // true')
  [ "$compare_enabled" = "true" ] && echo "CFG_COMPARE := 1" || echo "CFG_COMPARE := 0"
  
  local use_addr
  use_addr=$(echo "$config" | jq -r '.comparison.use_pass_fail_addr // true')
  [ "$use_addr" = "true" ] && echo "CFG_NO_ADDR := 0" || echo "CFG_NO_ADDR := 1"
  
  local spike
  spike=$(echo "$config" | jq -r '.comparison.spike_enabled // true')
  [ "$spike" = "true" ] && echo "CFG_SPIKE := 1" || echo "CFG_SPIKE := 0"
  
  echo ""
  
  # Trace settings
  echo "# Trace settings"
  local trace_enabled
  trace_enabled=$(echo "$config" | jq -r '.trace.enabled // true')
  [ "$trace_enabled" = "true" ] && echo "CFG_TRACE := 1" || echo "CFG_TRACE := 0"
  
  local trace_format
  trace_format=$(echo "$config" | jq -r '.trace.format // "fst"')
  echo "CFG_TRACE_FORMAT := $trace_format"
  
  local trace_depth
  trace_depth=$(echo "$config" | jq -r '.trace.depth // 99')
  echo "CFG_TRACE_DEPTH := $trace_depth"
  
  echo ""
  
  # Build settings
  echo "# Build settings"
  local mode
  mode=$(echo "$config" | jq -r '.build.mode // "debug"')
  echo "CFG_MODE := $mode"
  
  local opt
  opt=$(echo "$config" | jq -r '.build.opt_level // "-O0"')
  echo "CFG_OPT_LEVEL := $opt"
  
  echo ""
  
  # Logging flags (for backwards compatibility)
  echo "# Logging flags"
  local fast_sim
  fast_sim=$(echo "$config" | jq -r '.defines.FAST_SIM // false')
  [ "$fast_sim" = "true" ] && echo "CFG_FAST_SIM := 1" || echo "CFG_FAST_SIM := 0"
  
  local bp_log
  bp_log=$(echo "$config" | jq -r '.logging.bp_log // false')
  [ "$bp_log" = "true" ] && echo "CFG_BP_LOG := 1" || echo "CFG_BP_LOG := 0"
  
  local verbose
  verbose=$(echo "$config" | jq -r '.logging.verbose // false')
  [ "$verbose" = "true" ] && echo "CFG_VERBOSE := 1" || echo "CFG_VERBOSE := 0"
  
  echo ""
  
  # SV Defines
  echo "# SystemVerilog Defines"
  local defines
  defines=$(generate_defines "$config")
  echo "CFG_SV_DEFINES := $defines"
  
  echo ""
  
  # Test list path (if specified)
  local test_list
  test_list=$(echo "$config" | jq -r '.test_list // empty')
  if [ -n "$test_list" ]; then
    echo "# Test list"
    echo "CFG_TEST_LIST := \$(ROOT_DIR)/$test_list"
  fi
}

# -----------------------------------------
# Convert to environment exports
# -----------------------------------------
to_env_vars() {
  local config="$1"
  
  echo "# Export to source this file"
  
  local max_cycles
  max_cycles=$(echo "$config" | jq -r '.simulation.max_cycles // 10000')
  echo "export MAX_CYCLES=$max_cycles"
  
  local fast_sim
  fast_sim=$(echo "$config" | jq -r '.defines.FAST_SIM // false')
  [ "$fast_sim" = "true" ] && echo "export FAST_SIM=1" || echo "export FAST_SIM=0"
  
  local bp_log
  bp_log=$(echo "$config" | jq -r '.logging.bp_log // false')
  [ "$bp_log" = "true" ] && echo "export BP_LOG=1" || echo "export BP_LOG=0"
  
  local trace
  trace=$(echo "$config" | jq -r '.trace.enabled // true')
  [ "$trace" = "true" ] && echo "export TRACE=1" || echo "export TRACE=0"
  
  local mode
  mode=$(echo "$config" | jq -r '.build.mode // "debug"')
  echo "export MODE=$mode"
  
  local no_addr
  no_addr=$(echo "$config" | jq -r '.comparison.use_pass_fail_addr // true')
  [ "$no_addr" = "true" ] && echo "export NO_ADDR=0" || echo "export NO_ADDR=1"
}

# -----------------------------------------
# Main
# -----------------------------------------
main() {
  check_jq
  
  # Handle special flags first
  case "${1:-}" in
    --help|-h)
      usage
      exit 0
      ;;
    --list|-l)
      list_configs
      exit 0
      ;;
    "")
      usage
      exit 1
      ;;
  esac
  
  local config_name="$1"
  shift
  
  # Load config with inheritance
  local config
  config=$(load_config "$config_name")
  
  # Process remaining arguments
  case "${1:-}" in
    --make|-m)
      to_make_vars "$config"
      ;;
    --env|-e)
      to_env_vars "$config"
      ;;
    --get|-g)
      if [ -z "${2:-}" ]; then
        echo -e "${RED}[ERROR]${RESET} --get requires a path argument" >&2
        exit 1
      fi
      get_value "$config" "$2"
      ;;
    --defines|-d)
      generate_defines "$config"
      ;;
    --raw|-r)
      echo "$config" | jq .
      ;;
    "")
      # Default: show formatted output
      echo -e "${CYAN}Configuration: ${GREEN}$config_name${RESET}"
      echo ""
      echo "$config" | jq -C .
      ;;
    *)
      echo -e "${RED}[ERROR]${RESET} Unknown option: $1" >&2
      usage
      exit 1
      ;;
  esac
}

main "$@"
