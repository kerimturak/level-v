# ==============================================================
# CERES RISC-V — OpenLane Interactive Init Script
# ==============================================================
# Kullanım (interactive tclsh açıkken):
#   source /path/to/interactive_init.tcl
#
# Veya make asic_interactive otomatik olarak çalıştırır.
# ==============================================================

package require openlane

# Environment'tan parametreleri al (make asic_interactive tarafından set edilir)
if { [info exists ::env(CERES_DESIGN_DIR)] } {
    set design_dir $::env(CERES_DESIGN_DIR)
} else {
    puts "ERROR: CERES_DESIGN_DIR environment variable not set"
    puts "Use: make asic_interactive or make asic_interactive_raw"
    return
}

if { [info exists ::env(CERES_RUN_TAG)] } {
    set run_tag $::env(CERES_RUN_TAG)
} else {
    set run_tag "interactive_[clock format [clock seconds] -format %Y%m%d_%H%M%S]"
}

if { [info exists ::env(CERES_RUNS_DIR)] } {
    set runs_dir $::env(CERES_RUNS_DIR)
} else {
    puts "ERROR: CERES_RUNS_DIR environment variable not set"
    return
}

puts "\[CERES\] Preparing design..."
puts "\[CERES\]   Design : $design_dir"
puts "\[CERES\]   Tag    : $run_tag"
puts "\[CERES\]   Runs   : $runs_dir"

prep -design $design_dir -tag $run_tag -run_path $runs_dir -overwrite

puts ""
puts "\[CERES\] Ready! Available commands:"
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
