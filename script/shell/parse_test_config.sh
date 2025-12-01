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
  
  # Thread settings
  local build_threads
  build_threads=$(echo "$config" | jq -r '.simulation.build_threads // "auto"')
  if [ "$build_threads" = "auto" ]; then
    echo "CFG_BUILD_THREADS := \$(shell nproc 2>/dev/null || echo 4)"
  else
    echo "CFG_BUILD_THREADS := $build_threads"
  fi
  
  local sim_threads
  sim_threads=$(echo "$config" | jq -r '.simulation.sim_threads // 1')
  if [ "$sim_threads" = "auto" ]; then
    echo "CFG_SIM_THREADS := \$(shell nproc 2>/dev/null || echo 4)"
  else
    echo "CFG_SIM_THREADS := $sim_threads"
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
  
  # Spike Configuration
  echo "# Spike ISA Simulator Configuration"
  
  local spike_enabled
  spike_enabled=$(echo "$config" | jq -r '.spike.enabled // true')
  [ "$spike_enabled" = "true" ] && echo "CFG_SPIKE_ENABLED := 1" || echo "CFG_SPIKE_ENABLED := 0"
  
  local spike_isa
  spike_isa=$(echo "$config" | jq -r '.spike.isa // "rv32im_zicsr_zicntr_zifencei"')
  echo "CFG_SPIKE_ISA := $spike_isa"
  
  local spike_priv
  spike_priv=$(echo "$config" | jq -r '.spike.priv // "m"')
  echo "CFG_SPIKE_PRIV := $spike_priv"
  
  local spike_pc
  spike_pc=$(echo "$config" | jq -r '.spike.pc // "0x80000000"')
  echo "CFG_SPIKE_PC := $spike_pc"
  
  local spike_processors
  spike_processors=$(echo "$config" | jq -r '.spike.processors // 1')
  echo "CFG_SPIKE_PROCESSORS := $spike_processors"
  
  local spike_memory
  spike_memory=$(echo "$config" | jq -r '.spike.memory_mb // 256')
  echo "CFG_SPIKE_MEMORY_MB := $spike_memory"
  
  local spike_triggers
  spike_triggers=$(echo "$config" | jq -r '.spike.triggers // 1')
  echo "CFG_SPIKE_TRIGGERS := $spike_triggers"
  
  local spike_pmp_regions
  spike_pmp_regions=$(echo "$config" | jq -r '.spike.pmp_regions // 0')
  echo "CFG_SPIKE_PMP_REGIONS := $spike_pmp_regions"
  
  local spike_pmp_granularity
  spike_pmp_granularity=$(echo "$config" | jq -r '.spike.pmp_granularity // 4')
  echo "CFG_SPIKE_PMP_GRANULARITY := $spike_pmp_granularity"
  
  local spike_misaligned
  spike_misaligned=$(echo "$config" | jq -r '.spike.misaligned // false')
  [ "$spike_misaligned" = "true" ] && echo "CFG_SPIKE_MISALIGNED := 1" || echo "CFG_SPIKE_MISALIGNED := 0"
  
  local spike_big_endian
  spike_big_endian=$(echo "$config" | jq -r '.spike.big_endian // false')
  [ "$spike_big_endian" = "true" ] && echo "CFG_SPIKE_BIG_ENDIAN := 1" || echo "CFG_SPIKE_BIG_ENDIAN := 0"
  
  local spike_halted
  spike_halted=$(echo "$config" | jq -r '.spike.halted // false')
  [ "$spike_halted" = "true" ] && echo "CFG_SPIKE_HALTED := 1" || echo "CFG_SPIKE_HALTED := 0"
  
  local spike_log_commits
  spike_log_commits=$(echo "$config" | jq -r '.spike.log_commits // true')
  [ "$spike_log_commits" = "true" ] && echo "CFG_SPIKE_LOG_COMMITS := 1" || echo "CFG_SPIKE_LOG_COMMITS := 0"
  
  local spike_log_cache_miss
  spike_log_cache_miss=$(echo "$config" | jq -r '.spike.log_cache_miss // false')
  [ "$spike_log_cache_miss" = "true" ] && echo "CFG_SPIKE_LOG_CACHE_MISS := 1" || echo "CFG_SPIKE_LOG_CACHE_MISS := 0"
  
  local spike_debug_mode
  spike_debug_mode=$(echo "$config" | jq -r '.spike.debug_mode // true')
  [ "$spike_debug_mode" = "true" ] && echo "CFG_SPIKE_DEBUG_MODE := 1" || echo "CFG_SPIKE_DEBUG_MODE := 0"
  
  local spike_instructions
  spike_instructions=$(echo "$config" | jq -r '.spike.instructions_limit // 0')
  echo "CFG_SPIKE_INSTRUCTIONS := $spike_instructions"
  
  local spike_real_time_clint
  spike_real_time_clint=$(echo "$config" | jq -r '.spike.real_time_clint // false')
  [ "$spike_real_time_clint" = "true" ] && echo "CFG_SPIKE_REAL_TIME_CLINT := 1" || echo "CFG_SPIKE_REAL_TIME_CLINT := 0"
  
  local spike_blocksz
  spike_blocksz=$(echo "$config" | jq -r '.spike.blocksz // 64')
  echo "CFG_SPIKE_BLOCKSZ := $spike_blocksz"
  
  # Debug Module Settings
  echo ""
  echo "# Spike Debug Module Configuration"
  
  local dm_enabled
  dm_enabled=$(echo "$config" | jq -r '.spike.debug_module.enabled // false')
  [ "$dm_enabled" = "true" ] && echo "CFG_SPIKE_DM_ENABLED := 1" || echo "CFG_SPIKE_DM_ENABLED := 0"
  
  local dm_progsize
  dm_progsize=$(echo "$config" | jq -r '.spike.debug_module.progsize // 2')
  echo "CFG_SPIKE_DM_PROGSIZE := $dm_progsize"
  
  local dm_datacount
  dm_datacount=$(echo "$config" | jq -r '.spike.debug_module.datacount // 2')
  echo "CFG_SPIKE_DM_DATACOUNT := $dm_datacount"
  
  local dm_sba_bits
  dm_sba_bits=$(echo "$config" | jq -r '.spike.debug_module.sba_bits // 0')
  echo "CFG_SPIKE_DM_SBA_BITS := $dm_sba_bits"
  
  local dm_auth
  dm_auth=$(echo "$config" | jq -r '.spike.debug_module.auth // false')
  [ "$dm_auth" = "true" ] && echo "CFG_SPIKE_DM_AUTH := 1" || echo "CFG_SPIKE_DM_AUTH := 0"
  
  local dm_dmi_rti
  dm_dmi_rti=$(echo "$config" | jq -r '.spike.debug_module.dmi_rti // 0')
  echo "CFG_SPIKE_DM_DMI_RTI := $dm_dmi_rti"
  
  local dm_abstract_rti
  dm_abstract_rti=$(echo "$config" | jq -r '.spike.debug_module.abstract_rti // 0')
  echo "CFG_SPIKE_DM_ABSTRACT_RTI := $dm_abstract_rti"
  
  local dm_no_hasel
  dm_no_hasel=$(echo "$config" | jq -r '.spike.debug_module.no_hasel // false')
  [ "$dm_no_hasel" = "true" ] && echo "CFG_SPIKE_DM_NO_HASEL := 1" || echo "CFG_SPIKE_DM_NO_HASEL := 0"
  
  local dm_no_abstract_csr
  dm_no_abstract_csr=$(echo "$config" | jq -r '.spike.debug_module.no_abstract_csr // false')
  [ "$dm_no_abstract_csr" = "true" ] && echo "CFG_SPIKE_DM_NO_ABSTRACT_CSR := 1" || echo "CFG_SPIKE_DM_NO_ABSTRACT_CSR := 0"
  
  local dm_no_abstract_fpr
  dm_no_abstract_fpr=$(echo "$config" | jq -r '.spike.debug_module.no_abstract_fpr // false')
  [ "$dm_no_abstract_fpr" = "true" ] && echo "CFG_SPIKE_DM_NO_ABSTRACT_FPR := 1" || echo "CFG_SPIKE_DM_NO_ABSTRACT_FPR := 0"
  
  local dm_no_halt_groups
  dm_no_halt_groups=$(echo "$config" | jq -r '.spike.debug_module.no_halt_groups // false')
  [ "$dm_no_halt_groups" = "true" ] && echo "CFG_SPIKE_DM_NO_HALT_GROUPS := 1" || echo "CFG_SPIKE_DM_NO_HALT_GROUPS := 0"
  
  local dm_no_impebreak
  dm_no_impebreak=$(echo "$config" | jq -r '.spike.debug_module.no_impebreak // false')
  [ "$dm_no_impebreak" = "true" ] && echo "CFG_SPIKE_DM_NO_IMPEBREAK := 1" || echo "CFG_SPIKE_DM_NO_IMPEBREAK := 0"
  
  # Cache Settings
  echo ""
  echo "# Spike Cache Configuration"
  
  local cache_enabled
  cache_enabled=$(echo "$config" | jq -r '.spike.cache.enabled // false')
  [ "$cache_enabled" = "true" ] && echo "CFG_SPIKE_CACHE_ENABLED := 1" || echo "CFG_SPIKE_CACHE_ENABLED := 0"
  
  local icache
  icache=$(echo "$config" | jq -r '.spike.cache.icache // ""')
  echo "CFG_SPIKE_ICACHE := $icache"
  
  local dcache
  dcache=$(echo "$config" | jq -r '.spike.cache.dcache // ""')
  echo "CFG_SPIKE_DCACHE := $dcache"
  
  local l2cache
  l2cache=$(echo "$config" | jq -r '.spike.cache.l2cache // ""')
  echo "CFG_SPIKE_L2CACHE := $l2cache"
  
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
