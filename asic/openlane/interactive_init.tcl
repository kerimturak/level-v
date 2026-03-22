# ==============================================================
# Level RISC-V — OpenLane Interactive Init Script
# ==============================================================
# Usage (with interactive tclsh open):
#   source /path/to/interactive_init.tcl
#
# Or run via: make asic_interactive (runs this automatically).
# ==============================================================

package require openlane

# Read parameters from the environment (set by make asic_interactive)
if { [info exists ::env(LEVEL_DESIGN_DIR)] } {
    set design_dir $::env(LEVEL_DESIGN_DIR)
} else {
    puts "ERROR: LEVEL_DESIGN_DIR environment variable not set"
    puts "Use: make asic_interactive or make asic_interactive_raw"
    return
}

if { [info exists ::env(LEVEL_RUN_TAG)] } {
    set run_tag $::env(LEVEL_RUN_TAG)
} else {
    set run_tag "interactive_[clock format [clock seconds] -format %Y%m%d_%H%M%S]"
}

if { [info exists ::env(LEVEL_RUNS_DIR)] } {
    set runs_dir $::env(LEVEL_RUNS_DIR)
} else {
    puts "ERROR: LEVEL_RUNS_DIR environment variable not set"
    return
}

puts "\[LEVEL\] Preparing design..."
puts "\[LEVEL\]   Design : $design_dir"
puts "\[LEVEL\]   Tag    : $run_tag"
puts "\[LEVEL\]   Runs   : $runs_dir"

prep -design $design_dir -tag $run_tag -run_path $runs_dir -overwrite

puts ""
puts "\[LEVEL\] Ready! Available commands:"
puts "  run_synthesis              → Yosys synthesis"
puts "  run_floorplan              → Floorplan + macro placement"
puts "  run_placement              → Global + detailed placement"
puts "  run_cts                    → Clock tree synthesis"
puts "  run_routing                → Global + detailed routing"
puts "  run_parasitics_sta         → Parasitic STA"
puts "  run_magic                  → GDS streaming"
puts "  run_magic_spice_export     → SPICE export"
puts "  run_lvs                    → Layout vs Schematic"
puts "  run_magic_drc              → Design Rule Check"
puts "  run_antenna_check          → Antenna check"
puts "  save_final_views           → Save final outputs"
puts "  generate_final_summary_report → Final report"
puts ""
