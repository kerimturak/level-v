# ==============================================================
# CERES RISC-V — Synthesis + Floorplan Only
# Instance name discovery için kullanılır.
# ==============================================================

package require openlane

set design_dir $::env(CERES_DESIGN_DIR)
set runs_dir   $::env(CERES_RUNS_DIR)
set run_tag    "synth_discovery"

puts "\[CERES\] Synthesis + Floorplan only (for name discovery)"
puts "\[CERES\]   Design : $design_dir"
puts "\[CERES\]   Tag    : $run_tag"
puts "\[CERES\]   Runs   : $runs_dir"

prep -design $design_dir -tag $run_tag -run_path $runs_dir -overwrite

puts "\[CERES\] Running synthesis..."
run_synthesis

puts "\[CERES\] Running floorplan..."
run_floorplan

puts "\[CERES\] Done! Use 'make asic_dump_names' to extract instance names."
