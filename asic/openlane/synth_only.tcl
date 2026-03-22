# ==============================================================
# Level RISC-V — Synthesis + Floorplan Only
# Used for instance name discovery.
# ==============================================================

package require openlane

set design_dir $::env(LEVEL_DESIGN_DIR)
set runs_dir   $::env(LEVEL_RUNS_DIR)
set run_tag    "synth_discovery"

puts "\[LEVEL\] Synthesis + Floorplan only (for name discovery)"
puts "\[LEVEL\]   Design : $design_dir"
puts "\[LEVEL\]   Tag    : $run_tag"
puts "\[LEVEL\]   Runs   : $runs_dir"

prep -design $design_dir -tag $run_tag -run_path $runs_dir -overwrite

puts "\[LEVEL\] Running synthesis..."
run_synthesis

puts "\[LEVEL\] Running floorplan..."
run_floorplan

puts "\[LEVEL\] Done! Use 'make asic_dump_names' to extract instance names."
