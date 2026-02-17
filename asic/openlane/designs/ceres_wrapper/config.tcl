# ==============================================================
# CERES RISC-V OpenLane Configuration (SKY130)
# ==============================================================

set ::env(DESIGN_NAME) ceres_wrapper

set sv2v_file "$::env(DESIGN_DIR)/src/ceres_wrapper_sv2v.v"
if {[file exists $sv2v_file]} {
	set ::env(VERILOG_FILES) $sv2v_file
} else {
	set pkg_file "$::env(DESIGN_DIR)/src/ceres_param.sv"
	set rtl_files [glob $::env(DESIGN_DIR)/src/*.sv $::env(DESIGN_DIR)/src/*.v]
	set rtl_files [lsearch -all -inline -not -exact $rtl_files $pkg_file]
	set ::env(VERILOG_FILES) [concat [list $pkg_file] $rtl_files]
}
set ::env(VERILOG_INCLUDE_DIRS) "$::env(DESIGN_DIR)/src $::env(DESIGN_DIR)/src/include"
set ::env(SYNTH_DEFINES) "SYNTHESIS MINIMAL_SOC"

set ::env(CLOCK_PORT) clk_i
set ::env(CLOCK_NET) clk_i
set ::env(CLOCK_PERIOD) 20.0

set ::env(BASE_SDC_FILE) $::env(DESIGN_DIR)/constraint.sdc
set ::env(FP_PIN_ORDER_CFG) $::env(DESIGN_DIR)/pin_order.cfg

set ::env(FP_SIZING) relative
set ::env(FP_CORE_UTIL) 35
set ::env(FP_ASPECT_RATIO) 1.0
set ::env(PL_TARGET_DENSITY) 0.45

set ::env(SYNTH_STRATEGY) "AREA 1"
set ::env(SYNTH_MAX_FANOUT) 12
set ::env(RUN_LINTER) 0

set ::env(RUN_CTS) 1
set ::env(RUN_DRT) 1
set ::env(RUN_LVS) 1
set ::env(RUN_MAGIC_DRC) 1
set ::env(RUN_MAGIC) 1
set ::env(FP_PDN_AUTO_ADJUST) 1
