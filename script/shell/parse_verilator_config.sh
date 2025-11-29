#!/usr/bin/env bash
# =========================================
# CERES RISC-V — Verilator Config Parser
# =========================================
# Reads verilator.json and outputs Make-compatible variables
# or exports them as environment variables
#
# Usage:
#   source $(./parse_verilator_config.sh)           # Export to env
#   ./parse_verilator_config.sh --make              # Output for Make
#   ./parse_verilator_config.sh --profile fast      # Use specific profile
#   ./parse_verilator_config.sh --get simulation.max_cycles  # Get single value
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CONFIG_DIR="${SCRIPT_DIR}/../config"
DEFAULT_CONFIG="${CONFIG_DIR}/verilator.json"
USER_CONFIG="${CONFIG_DIR}/verilator.local.json"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
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
# Merge configs (user overrides default)
# -----------------------------------------
merge_configs() {
  local base="$1"
  local override="$2"
  
  if [ -f "$override" ]; then
    jq -s '.[0] * .[1]' "$base" "$override"
  else
    cat "$base"
  fi
}

# -----------------------------------------
# Apply profile to config
# -----------------------------------------
apply_profile() {
  local config="$1"
  local profile="$2"
  
  # Extract profile and merge with base config
  echo "$config" | jq --arg p "$profile" '
    . as $base |
    if .profiles[$p] then
      .profiles[$p] as $profile |
      reduce (["simulation", "build", "trace", "coverage", "optimization", "features", "logging", "warnings"] | .[]) as $section (
        $base;
        if $profile[$section] then
          .[$section] = (.[$section] // {}) * $profile[$section]
        else
          .
        end
      )
    else
      error("Profile not found: \($p)")
    end
  '
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
# Convert to Make variables
# -----------------------------------------
to_make_vars() {
  local config="$1"
  
  echo "$config" | jq -r '
    # Helper to convert value to make format
    def to_make_val:
      if type == "boolean" then (if . then "1" else "0" end)
      elif type == "number" then tostring
      elif . == "auto" then ""
      else tostring
      end;
    
    # Simulation
    "# Simulation settings",
    "VERILATOR_MAX_CYCLES := \(.simulation.max_cycles // 100000)",
    "VERILATOR_TIMEOUT := \(.simulation.timeout // 0)",
    (if .simulation.threads != "auto" and .simulation.threads != null then "VERILATOR_THREADS := \(.simulation.threads)" else empty end),
    (if .simulation.seed != "auto" and .simulation.seed != null then "VERILATOR_SEED := \(.simulation.seed)" else empty end),
    "",
    
    # Build
    "# Build settings",
    "MODE := \(.build.mode // "release")",
    (if .build.jobs != "auto" and .build.jobs != null then "BUILD_JOBS := \(.build.jobs)" else empty end),
    "OPT_LEVEL := \(.build.opt_level // "-O3")",
    "CPP_STD := \(.build.cpp_standard // "c++17")",
    "",
    
    # Trace
    "# Trace settings",
    "TRACE_ENABLED := \(if .trace.enabled then "1" else "0" end)",
    "TRACE_FORMAT := \(.trace.format // "fst")",
    "TRACE_DEPTH := \(.trace.depth // 99)",
    "TRACE_STRUCTS := \(if .trace.structs then "1" else "0" end)",
    "TRACE_PARAMS := \(if .trace.params then "1" else "0" end)",
    (if .trace.threads > 1 then "TRACE_THREADS := 1" else empty end),
    "",
    
    # Coverage
    "# Coverage settings",
    (if .coverage.enabled then "COVERAGE := 1" else empty end),
    "",
    
    # Optimization
    "# Optimization settings",
    "OUTPUT_SPLIT := \(.optimization.output_split // 20000)",
    "OUTPUT_SPLIT_CFUNC := \(.optimization.output_split_cfuncs // 5000)",
    "UNROLL_COUNT := \(.optimization.unroll_count // 64)",
    "UNROLL_STMTS := \(.optimization.unroll_stmts // 30000)",
    "X_ASSIGN := \(.optimization.x_assign // "fast")",
    "X_INITIAL := \(.optimization.x_initial // "fast")",
    "",
    
    # Features
    "# Feature flags",
    (if .features.vpi then "VPI := 1" else empty end),
    (if .features.hierarchical then "HIERARCHICAL := 1" else empty end),
    (if .features.debug_check then "DEBUG_CHECK := 1" else empty end),
    "",
    
    # Logging
    "# Logging settings",
    (if .logging.fast_sim then "FAST_SIM := 1" else empty end),
    (if .logging.bp_log then "BP_LOG := 1" else empty end),
    (if .logging.bp_verbose then "BP_VERBOSE := 1" else empty end)
  ' | grep -v '^$' | grep -v '^#' || true
  
  # Also output comments for readability
  echo "$config" | jq -r '
    "# Simulation settings",
    "# Build settings", 
    "# Trace settings",
    "# Coverage settings",
    "# Optimization settings",
    "# Feature flags",
    "# Logging settings"
  ' 2>/dev/null || true
}

# -----------------------------------------
# Convert to environment exports
# -----------------------------------------
to_env_exports() {
  local config="$1"
  
  echo "$config" | jq -r '
    def to_env_val:
      if type == "boolean" then (if . then "1" else "0" end)
      elif type == "number" then tostring
      elif . == "auto" then ""
      else tostring
      end;
    
    "export VERILATOR_MAX_CYCLES=\"\(.simulation.max_cycles // 100000)\"",
    "export VERILATOR_TIMEOUT=\"\(.simulation.timeout // 0)\"",
    (if .simulation.threads != "auto" then "export VERILATOR_THREADS=\"\(.simulation.threads)\"" else empty end),
    (if .simulation.seed != "auto" then "export VERILATOR_SEED=\"\(.simulation.seed)\"" else empty end),
    "export MODE=\"\(.build.mode // "release")\"",
    "export OPT_LEVEL=\"\(.build.opt_level // "-O3")\"",
    "export TRACE_ENABLED=\"\(if .trace.enabled then "1" else "0" end)\"",
    "export TRACE_DEPTH=\"\(.trace.depth // 99)\"",
    (if .coverage.enabled then "export COVERAGE=\"1\"" else empty end),
    (if .logging.fast_sim then "export FAST_SIM=\"1\"" else empty end),
    (if .logging.bp_log then "export BP_LOG=\"1\"" else empty end)
  '
}

# -----------------------------------------
# List available profiles
# -----------------------------------------
list_profiles() {
  local config="$1"
  
  echo -e "${GREEN}Available profiles:${RESET}"
  echo "$config" | jq -r '.profiles | to_entries[] | "  \(.key): \(.value._description // "No description")"'
}

# -----------------------------------------
# Show current config summary
# -----------------------------------------
show_summary() {
  local config="$1"
  
  echo -e "${GREEN}═══════════════════════════════════════${RESET}"
  echo -e "${GREEN}  Verilator Configuration Summary${RESET}"
  echo -e "${GREEN}═══════════════════════════════════════${RESET}"
  echo ""
  
  echo "$config" | jq -r '
    "Simulation:",
    "  Max Cycles: \(.simulation.max_cycles)",
    "  Timeout:    \(.simulation.timeout)s",
    "  Threads:    \(.simulation.threads)",
    "",
    "Build:",
    "  Mode:       \(.build.mode)",
    "  Opt Level:  \(.build.opt_level)",
    "",
    "Trace:",
    "  Enabled:    \(.trace.enabled)",
    "  Format:     \(.trace.format)",
    "  Depth:      \(.trace.depth)",
    "",
    "Features:",
    "  Coverage:   \(.coverage.enabled)",
    "  VPI:        \(.features.vpi)",
    "  Fast Sim:   \(.logging.fast_sim)",
    "  BP Log:     \(.logging.bp_log)"
  '
}

# -----------------------------------------
# Main
# -----------------------------------------
main() {
  check_jq
  
  local output_mode="env"
  local profile=""
  local get_path=""
  local show_help=false
  local show_profiles=false
  local show_config_summary=false
  
  # Parse arguments
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --make|-m)
        output_mode="make"
        shift
        ;;
      --env|-e)
        output_mode="env"
        shift
        ;;
      --profile|-p)
        profile="$2"
        shift 2
        ;;
      --get|-g)
        get_path="$2"
        shift 2
        ;;
      --list-profiles|-l)
        show_profiles=true
        shift
        ;;
      --summary|-s)
        show_config_summary=true
        shift
        ;;
      --config|-c)
        DEFAULT_CONFIG="$2"
        shift 2
        ;;
      --help|-h)
        show_help=true
        shift
        ;;
      *)
        echo -e "${RED}Unknown option: $1${RESET}" >&2
        exit 1
        ;;
    esac
  done
  
  if [ "$show_help" = true ]; then
    echo "Usage: $(basename "$0") [OPTIONS]"
    echo ""
    echo "Options:"
    echo "  -m, --make              Output Make-compatible variables"
    echo "  -e, --env               Output environment exports (default)"
    echo "  -p, --profile NAME      Apply named profile"
    echo "  -g, --get PATH          Get single value (e.g., simulation.max_cycles)"
    echo "  -l, --list-profiles     List available profiles"
    echo "  -s, --summary           Show configuration summary"
    echo "  -c, --config FILE       Use custom config file"
    echo "  -h, --help              Show this help"
    echo ""
    echo "Examples:"
    echo "  $(basename "$0") --make --profile fast"
    echo "  $(basename "$0") --get simulation.max_cycles"
    echo "  eval \$($(basename "$0") --env)"
    exit 0
  fi
  
  # Check config exists
  if [ ! -f "$DEFAULT_CONFIG" ]; then
    echo -e "${RED}[ERROR]${RESET} Config not found: $DEFAULT_CONFIG" >&2
    exit 1
  fi
  
  # Load and merge config
  local config
  config=$(merge_configs "$DEFAULT_CONFIG" "$USER_CONFIG")
  
  # List profiles
  if [ "$show_profiles" = true ]; then
    list_profiles "$config"
    exit 0
  fi
  
  # Apply profile if specified
  if [ -n "$profile" ]; then
    config=$(apply_profile "$config" "$profile")
  fi
  
  # Show summary
  if [ "$show_config_summary" = true ]; then
    show_summary "$config"
    exit 0
  fi
  
  # Get single value
  if [ -n "$get_path" ]; then
    get_value "$config" "$get_path"
    exit 0
  fi
  
  # Output based on mode
  case "$output_mode" in
    make)
      to_make_vars "$config"
      ;;
    env)
      to_env_exports "$config"
      ;;
  esac
}

main "$@"
