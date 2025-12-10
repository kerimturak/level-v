# ============================================================================
# Timing Optimization Script for Vivado Synthesis and Implementation
# ============================================================================
# This script applies aggressive timing optimization strategies to improve
# the critical path timing in the CERES processor
#
# Usage:
#   source scripts/timing_optimization.tcl
#
# Or add to your synthesis/implementation run properties

# ============================================================================
# SYNTHESIS OPTIMIZATIONS
# ============================================================================

# Enable register retiming (moves registers through combinational logic)
set_property STEPS.SYNTH_DESIGN.ARGS.RETIMING true [get_runs synth_1]

# Use aggressive synthesis directive for better QoR
set_property STEPS.SYNTH_DESIGN.ARGS.DIRECTIVE PerformanceOptimized [get_runs synth_1]

# Enable FSM extraction and optimization
set_property STEPS.SYNTH_DESIGN.ARGS.FSM_EXTRACTION one_hot [get_runs synth_1]

# Resource sharing off for critical paths (may increase area but improves timing)
set_property STEPS.SYNTH_DESIGN.ARGS.RESOURCE_SHARING off [get_runs synth_1]

# Enable no-lut-combine for better timing on critical paths
set_property STEPS.SYNTH_DESIGN.ARGS.NO_LC false [get_runs synth_1]

# Flatten hierarchy where beneficial for timing
set_property STEPS.SYNTH_DESIGN.ARGS.FLATTEN_HIERARCHY rebuilt [get_runs synth_1]

# ============================================================================
# IMPLEMENTATION OPTIMIZATIONS
# ============================================================================

# Enable physical optimization in opt_design
set_property STEPS.OPT_DESIGN.IS_ENABLED true [get_runs impl_1]
set_property STEPS.OPT_DESIGN.ARGS.DIRECTIVE ExploreWithRemap [get_runs impl_1]

# Enable placement with timing-driven directive
set_property STEPS.PLACE_DESIGN.ARGS.DIRECTIVE ExtraTimingOpt [get_runs impl_1]

# Enable physical optimization after placement
set_property STEPS.PHYS_OPT_DESIGN.IS_ENABLED true [get_runs impl_1]
set_property STEPS.PHYS_OPT_DESIGN.ARGS.DIRECTIVE AggressiveExplore [get_runs impl_1]

# Enable aggressive routing
set_property STEPS.ROUTE_DESIGN.ARGS.DIRECTIVE AggressiveExplore [get_runs impl_1]

# Enable post-route physical optimization
set_property STEPS.POST_ROUTE_PHYS_OPT_DESIGN.IS_ENABLED true [get_runs impl_1]
set_property STEPS.POST_ROUTE_PHYS_OPT_DESIGN.ARGS.DIRECTIVE AggressiveExplore [get_runs impl_1]

# ============================================================================
# STRATEGY SELECTION
# ============================================================================

# Apply performance-focused implementation strategy
set_property STRATEGY Performance_ExplorePostRoutePhysOpt [get_runs impl_1]

puts "INFO: Timing optimization settings applied to synthesis and implementation runs"
puts "INFO: - Synthesis: PerformanceOptimized directive with retiming enabled"
puts "INFO: - Implementation: Performance_ExplorePostRoutePhysOpt strategy"
puts "INFO: - Physical optimization enabled in multiple stages"

# ============================================================================
# DESIGN-SPECIFIC OPTIMIZATIONS
# ============================================================================

# These commands should be run after synthesis/before implementation
# Uncomment and customize as needed after analyzing your specific design

# Example: Set max delay on critical paths
# set_max_delay -from [get_pins -hierarchical -filter {NAME =~ "*pipe2_reg*"}] \
#               -to [get_pins -hierarchical -filter {NAME =~ "*pc_reg*"}] 35.0

# Example: Set false paths (if applicable)
# set_false_path -from [get_clocks clk_i] -to [get_clocks <other_clock>]

# Example: Clock uncertainty reduction (if your clock is stable)
# set_clock_uncertainty -setup 0.050 [get_clocks clk_out1_clk_wiz_0]
# set_clock_uncertainty -hold 0.030 [get_clocks clk_out1_clk_wiz_0]
