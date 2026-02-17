# ==============================================================
# OpenLane Interactive Resume Script
# Resumes from Global Routing (Step 19) after system crash
# Run: run_20260217_200348
# ==============================================================

package require openlane

# Load existing run with the same tag (this restores all env vars)
prep -design /home/kerim/level-v/asic/openlane/designs/ceres_wrapper \
     -tag run_20260217_200348 \
     -run_path /home/kerim/level-v/results/asic/openlane/ceres_wrapper/runs \
     -overwrite

# Verify state is loaded correctly
puts "\[RESUME\]: CURRENT_DEF  = $::env(CURRENT_DEF)"
puts "\[RESUME\]: CURRENT_ODB  = $::env(CURRENT_ODB)"
puts "\[RESUME\]: CURRENT_INDEX = $::env(CURRENT_INDEX)"

# ============================================================
# STEP: Routing (global + fill + detailed + SPEF)
# ============================================================
puts "\[RESUME\]: Starting run_routing..."
run_routing

# ============================================================
# STEP: Parasitic STA (multi-corner)
# ============================================================
puts "\[RESUME\]: Running SPEF-based STA..."
run_parasitics_sta

# ============================================================
# STEP: IR Drop Report
# ============================================================
if { $::env(RUN_IRDROP_REPORT) } {
    puts "\[RESUME\]: Running IR Drop report..."
    run_irdrop_report
}

# ============================================================
# STEP: Magic GDS streaming
# ============================================================
if { $::env(RUN_MAGIC) } {
    puts "\[RESUME\]: Running Magic..."
    run_magic
}

# ============================================================
# STEP: KLayout GDS streaming + XOR
# ============================================================
if { $::env(RUN_KLAYOUT) } {
    puts "\[RESUME\]: Running KLayout..."
    run_klayout
}
if { $::env(RUN_KLAYOUT_XOR) } {
    puts "\[RESUME\]: Running KLayout XOR..."
    run_klayout_gds_xor
}

# ============================================================
# STEP: Magic SPICE export + LVS
# ============================================================
puts "\[RESUME\]: Running Magic SPICE export..."
run_magic_spice_export

if { $::env(RUN_LVS) } {
    puts "\[RESUME\]: Running LVS..."
    run_lvs
}

# ============================================================
# STEP: DRC
# ============================================================
if { $::env(RUN_MAGIC_DRC) } {
    puts "\[RESUME\]: Running Magic DRC..."
    run_magic_drc
}

if { $::env(RUN_KLAYOUT_DRC) } {
    puts "\[RESUME\]: Running KLayout DRC..."
    run_klayout_drc
}

# ============================================================
# STEP: Antenna Check
# ============================================================
puts "\[RESUME\]: Running antenna check..."
run_antenna_check

# ============================================================
# STEP: ERC (CVC)
# ============================================================
if { $::env(RUN_CVC) } {
    puts "\[RESUME\]: Running CVC ERC..."
    run_erc
}

# ============================================================
# Final reports and views
# ============================================================
puts "\[RESUME\]: Saving final views..."
save_final_views
calc_total_runtime
save_state
generate_final_summary_report

# Timing check
check_timing_violations \
    -quit_on_hold_vios [expr $::env(QUIT_ON_TIMING_VIOLATIONS) && $::env(QUIT_ON_HOLD_VIOLATIONS)] \
    -quit_on_setup_vios [expr $::env(QUIT_ON_TIMING_VIOLATIONS) && $::env(QUIT_ON_SETUP_VIOLATIONS)]

puts "\[RESUME\]: Flow completed successfully!"
