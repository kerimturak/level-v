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
set ::env(SYNTH_DEFINES) "SYNTHESIS MINIMAL_SOC CERES_OPENLANE"

set ::env(CLOCK_PORT) clk_i
set ::env(CLOCK_NET) clk_i
set ::env(CLOCK_PERIOD) 25.0

set ::env(BASE_SDC_FILE) $::env(DESIGN_DIR)/constraint.sdc
set ::env(PNR_SDC_FILE) $::env(DESIGN_DIR)/constraint.sdc
set ::env(SIGNOFF_SDC_FILE) $::env(DESIGN_DIR)/constraint.sdc
set ::env(FP_PIN_ORDER_CFG) $::env(DESIGN_DIR)/pin_order.cfg

set sram_macro_dir "$::env(DESIGN_DIR)/macros/sky130_sram_1kbyte_1rw1r_32x256_8"
set sram_lef "$sram_macro_dir/sky130_sram_1kbyte_1rw1r_32x256_8.lef"
set sram_gds "$sram_macro_dir/sky130_sram_1kbyte_1rw1r_32x256_8.gds"
set sram_lib "$sram_macro_dir/sky130_sram_1kbyte_1rw1r_32x256_8_TT_1p8V_25C.lib"
set sram_bb  "$::env(DESIGN_DIR)/src/sky130_sram_1kbyte_1rw1r_32x256_8.bb.sv"

if { [file exists $sram_lef] && [file exists $sram_gds] && [file exists $sram_lib] } {
	set ::env(EXTRA_LEFS) [list $sram_lef]
	set ::env(EXTRA_GDS_FILES) [list $sram_gds]
	set ::env(EXTRA_LIBS) [list $sram_lib]
	if { [file exists $sram_bb] } {
		set ::env(VERILOG_FILES_BLACKBOX) [list $sram_bb]
	}
	set ::env(FP_PDN_ENABLE_MACROS_GRID) 1
	set ::env(FP_PDN_MACRO_HOOKS) ".*i_main_sram_bank.* VPWR VGND vccd1 vssd1,.*i_sram.* VPWR VGND vccd1 vssd1"
}

set ::env(FP_SIZING) relative
set ::env(FP_CORE_UTIL) 28
set ::env(FP_ASPECT_RATIO) 1.0
set ::env(PL_TARGET_DENSITY) 0.35

set ::env(SYNTH_STRATEGY) "AREA 1"
set ::env(MAX_FANOUT_CONSTRAINT) 12
set ::env(SYNTH_NO_FLAT) 1
set ::env(SYNTH_BUFFERING) 0
set ::env(SYNTH_PARAMETERS) [list RAM_SIZE_KB=4 TIMER_EN=0]
set ::env(RUN_LINTER) 0

# sv2v parametric-type mangling ürettiği karmaşık ifadeler Yosys'un
# default parametrelerle RTLIL üretirken false-positive "out of bounds"
# uyarıları oluşturuyor. Asıl elaboration doğru parametrelerle çalışır.
set ::env(QUIT_ON_SYNTH_CHECKS) 0

set ::env(RUN_CTS) 1
set ::env(RUN_DRT) 1
set ::env(RUN_LVS) 1
set ::env(RUN_MAGIC_DRC) 1
set ::env(RUN_MAGIC) 1
set ::env(FP_PDN_AUTO_ADJUST) 1
