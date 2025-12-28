# =============================================================================
# ModelSim DO Script for DCache Verification
# =============================================================================

# Create work library if it doesn't exist
quietly if {[file exists work]} {
    vdel -all
}
vlib work

# Compile packages
vlog -sv +incdir+../../rtl/pkg \
    ../../rtl/pkg/ceres_pkg.sv \
    ../../rtl/pkg/ceres_param.sv

# Compile RTL
vlog -sv +incdir+../../rtl/pkg \
    ../../rtl/core/mmu/dcache.sv

# Compile testbench
vlog -sv +incdir+../../rtl/pkg \
    dcache_model.sv \
    tb_dcache.sv

# Load simulation
vsim -voptargs=+acc work.tb_dcache

# Add waves - organized by hierarchy
add wave -divider "Clock & Reset"
add wave -color Yellow /tb_dcache/clk
add wave -color Yellow /tb_dcache/rst_n

add wave -divider "Cache Request Interface"
add wave -radix hex /tb_dcache/cache_req_valid
add wave -radix hex /tb_dcache/cache_req_ready
add wave -radix hex /tb_dcache/cache_req_addr
add wave -radix bin /tb_dcache/cache_req_rw
add wave -radix unsigned /tb_dcache/cache_req_size
add wave -radix hex /tb_dcache/cache_req_data

add wave -divider "Cache Response Interface"
add wave -radix hex /tb_dcache/cache_res_valid
add wave -radix hex /tb_dcache/cache_res_data
add wave -radix bin /tb_dcache/cache_res_miss

add wave -divider "Lower Memory Interface"
add wave -radix hex /tb_dcache/lowx_req_valid
add wave -radix hex /tb_dcache/lowx_req_ready
add wave -radix hex /tb_dcache/lowx_req_addr
add wave -radix bin /tb_dcache/lowx_req_rw
add wave -radix hex /tb_dcache/lowx_req_data

add wave -radix hex /tb_dcache/lowx_res_valid
add wave -radix hex /tb_dcache/lowx_res_data

add wave -divider "Reference Model"
add wave -radix hex /tb_dcache/model/data_array
add wave -radix hex /tb_dcache/model/dirty_array
add wave -radix hex /tb_dcache/model/plru_array

# TODO: Add DUT internal signals when dcache is instantiated
# add wave -divider "DUT Internals"
# add wave -radix hex /tb_dcache/dut/...

# Configure wave window
configure wave -namecolwidth 250
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1

# Run simulation
run -all

# Zoom to fit
wave zoom full
