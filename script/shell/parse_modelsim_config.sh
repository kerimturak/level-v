#!/usr/bin/env bash
# =========================================
# CERES RISC-V — ModelSim Config Parser
# =========================================
# Reads modelsim.json and outputs Make-compatible variables
# or exports them as environment variables
#
# Usage:
#   source $(./parse_modelsim_config.sh)           # Export to env
#   ./parse_modelsim_config.sh --make              # Output for Make
#   ./parse_modelsim_config.sh --profile debug     # Use specific profile
#   ./parse_modelsim_config.sh --get lint.mode     # Get single value
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CONFIG_DIR="${SCRIPT_DIR}/../config"
DEFAULT_CONFIG="${CONFIG_DIR}/modelsim.json"
USER_CONFIG="${CONFIG_DIR}/modelsim.local.json"

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
      reduce (["simulation", "compile", "lint", "debug", "coverage", "language", "gls", "messages", "multicore"] | .[]) as $section (
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
      else tostring
      end;
    
    # Build coverage spec string (s=statement, b=branch, etc.)
    def coverage_spec:
      [
        (if .coverage.statement then "s" else empty end),
        (if .coverage.branch then "b" else empty end),
        (if .coverage.condition then "c" else empty end),
        (if .coverage.expression then "e" else empty end),
        (if .coverage.fsm then "f" else empty end),
        (if .coverage.toggle then "t" else empty end)
      ] | join("");
    
    # Simulation settings
    "MODELSIM_TIME_RES ?= \(.simulation.time_resolution // "ns")",
    "SIM_TIME ?= \(.simulation.sim_time // "100us")",
    "MODELSIM_VOPTARGS ?= \(.simulation.voptargs // "+acc=npr")",
    (if .simulation.quiet then "MODELSIM_QUIET ?= -quiet" else empty end),
    "",
    
    # Compile settings
    "MODELSIM_SV_MODE ?= \(if .compile.sv_mode then "-sv" else "" end)",
    "MODELSIM_MFCU ?= \(if .compile.mfcu then "-mfcu" else "-sfcu" end)",
    "MODELSIM_SVINPUTPORT ?= \(.compile.svinputport // "relaxed")",
    "",
    
    # Lint settings
    "MODELSIM_LINT_ENABLED ?= \(if .lint.enabled then "1" else "0" end)",
    "MODELSIM_LINT_MODE ?= \(.lint.mode // "default")",
    "MODELSIM_PEDANTIC ?= \(if .lint.pedantic then "-pedanticerrors" else "" end)",
    "",
    
    # Debug settings
    "MODELSIM_ACC ?= \(.debug.acc // "npr")",
    (if .debug.fsmdebug then "MODELSIM_FSMDEBUG ?= -fsmdebug" else empty end),
    (if .debug.classdebug then "MODELSIM_CLASSDEBUG ?= -classdebug" else empty end),
    (if .debug.assertdebug then "MODELSIM_ASSERTDEBUG ?= -assertdebug" else empty end),
    "",
    
    # Coverage settings
    (if .coverage.enabled then 
      "MODELSIM_COVERAGE ?= +cover=\(coverage_spec)"
    else 
      "MODELSIM_COVERAGE ?=" 
    end),
    "",
    
    # Language settings
    "MODELSIM_SV_COMPAT ?= -\(.language.sv_standard // "sv12compat")",
    "MODELSIM_TIMESCALE ?= \(.language.timescale // "1ns/1ps")",
    "",
    
    # GLS settings
    (if .gls.timing_checks == false then "MODELSIM_NOTIMINGCHECKS ?= +notimingchecks" else empty end),
    (if .gls.specify_delays == false then "MODELSIM_NOSPECIFY ?= +nospecify" else empty end),
    (if .gls.delay_mode == "min" then "MODELSIM_DELAY_MODE ?= +mindelays"
     elif .gls.delay_mode == "max" then "MODELSIM_DELAY_MODE ?= +maxdelays"
     elif .gls.delay_mode == "typ" then "MODELSIM_DELAY_MODE ?= +typdelays"
     elif .gls.delay_mode == "zero" then "MODELSIM_DELAY_MODE ?= +delay_mode_zero"
     elif .gls.delay_mode == "unit" then "MODELSIM_DELAY_MODE ?= +delay_mode_unit"
     else empty end),
    "",
    
    # Message suppressions
    "MODELSIM_SUPPRESS ?= \(.messages.suppress | map("-suppress \(.)") | join(" "))",
    (if (.messages.nowarn | length) > 0 then 
      "MODELSIM_NOWARN ?= \(.messages.nowarn | map("-nowarn \(.)") | join(" "))"
    else empty end),
    (if .messages.source_on_error then "MODELSIM_SOURCE ?= -source" else empty end),
    "",
    
    # Multicore settings
    (if .multicore.enabled then "MODELSIM_MULTICORE ?= -mtc \(.multicore.threads // 2)" else empty end)
  '
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
      else tostring
      end;
    
    "export MODELSIM_TIME_RES=\"\(.simulation.time_resolution // "ns")\"",
    "export SIM_TIME=\"\(.simulation.sim_time // "100us")\"",
    "export MODELSIM_LINT_ENABLED=\"\(if .lint.enabled then "1" else "0" end)\"",
    "export MODELSIM_LINT_MODE=\"\(.lint.mode // "default")\"",
    (if .coverage.enabled then "export MODELSIM_COVERAGE=\"1\"" else empty end)
  '
}

# -----------------------------------------
# List available profiles
# -----------------------------------------
list_profiles() {
  local config="$1"
  
  echo -e "${GREEN}Available profiles:${RESET}"
  echo "$config" | jq -r '
    .profiles | to_entries[] | 
    "  \(.key): \(.value._description // "No description")"
  '
}

# -----------------------------------------
# Print human-readable summary
# -----------------------------------------
print_summary() {
  local config="$1"
  
  echo -e "${GREEN}════════════════════════════════════════${RESET}"
  echo -e "${GREEN}  ModelSim Configuration Summary${RESET}"
  echo -e "${GREEN}════════════════════════════════════════${RESET}"
  
  echo "$config" | jq -r '
    "",
    "Simulation:",
    "  Time Resolution: \(.simulation.time_resolution // "ns")",
    "  Sim Time:        \(.simulation.sim_time // "100us")",
    "",
    "Compile:",
    "  SV Mode:    \(if .compile.sv_mode then "Enabled" else "Disabled" end)",
    "  MFCU:       \(if .compile.mfcu then "Multi-file" else "Single-file" end)",
    "  Opt Level:  \(.compile.opt_level // "O4")",
    "",
    "Lint:",
    "  Enabled: \(if .lint.enabled then "Yes" else "No" end)",
    "  Mode:    \(.lint.mode // "default")",
    "",
    "Coverage:",
    "  Enabled: \(if .coverage.enabled then "Yes" else "No" end)",
    ""
  '
}

# -----------------------------------------
# Validate configuration
# -----------------------------------------
validate_config() {
  local config="$1"
  
  # Check required fields
  echo "$config" | jq -e '.simulation and .compile and .lint' > /dev/null 2>&1 || {
    echo -e "${RED}[ERROR]${RESET} Invalid configuration: missing required sections" >&2
    return 1
  }
  
  # Validate lint mode
  local lint_mode
  lint_mode=$(echo "$config" | jq -r '.lint.mode // "default"')
  case "$lint_mode" in
    default|fast|full) ;;
    *) 
      echo -e "${YELLOW}[WARN]${RESET} Unknown lint mode: $lint_mode" >&2
      ;;
  esac
  
  return 0
}

# -----------------------------------------
# Main
# -----------------------------------------
main() {
  check_jq
  
  local mode="make"
  local profile=""
  local get_path=""
  local config_file="$DEFAULT_CONFIG"
  
  # Parse arguments
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --make)
        mode="make"
        shift
        ;;
      --env)
        mode="env"
        shift
        ;;
      --profile)
        profile="$2"
        shift 2
        ;;
      --get)
        mode="get"
        get_path="$2"
        shift 2
        ;;
      --list-profiles)
        mode="list"
        shift
        ;;
      --summary)
        mode="summary"
        shift
        ;;
      --validate)
        mode="validate"
        shift
        ;;
      --config)
        config_file="$2"
        shift 2
        ;;
      --help|-h)
        echo "Usage: $0 [OPTIONS]"
        echo ""
        echo "Options:"
        echo "  --make              Output Make-compatible variables (default)"
        echo "  --env               Output environment exports"
        echo "  --profile NAME      Apply specified profile"
        echo "  --get PATH          Get single value (e.g., lint.mode)"
        echo "  --list-profiles     List available profiles"
        echo "  --summary           Print configuration summary"
        echo "  --validate          Validate configuration"
        echo "  --config FILE       Use specified config file"
        echo "  --help              Show this help"
        exit 0
        ;;
      *)
        echo -e "${RED}[ERROR]${RESET} Unknown option: $1" >&2
        exit 1
        ;;
    esac
  done
  
  # Check config file exists
  if [ ! -f "$config_file" ]; then
    echo -e "${RED}[ERROR]${RESET} Config file not found: $config_file" >&2
    exit 1
  fi
  
  # Load and merge config
  local config
  config=$(merge_configs "$config_file" "$USER_CONFIG")
  
  # Apply profile if specified
  if [ -n "$profile" ]; then
    config=$(apply_profile "$config" "$profile")
  fi
  
  # Execute requested mode
  case "$mode" in
    make)
      to_make_vars "$config"
      ;;
    env)
      to_env_exports "$config"
      ;;
    get)
      get_value "$config" "$get_path"
      ;;
    list)
      list_profiles "$config"
      ;;
    summary)
      print_summary "$config"
      ;;
    validate)
      if validate_config "$config"; then
        echo -e "${GREEN}[OK]${RESET} Configuration is valid"
      else
        exit 1
      fi
      ;;
  esac
}

main "$@"
