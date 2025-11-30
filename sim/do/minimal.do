##################################################################################
#                     CERES RISC-V — Minimal Quick Debug                        #
##################################################################################
# Ultra-fast loading, essential signals only
##################################################################################

set TB   "sim:/tb_wrapper"
set SOC  "$TB/ceres_wrapper/i_soc"

configure wave -namecolwidth 280
configure wave -valuecolwidth 100
configure wave -timelineunits ns

# ═══════════ ESSENTIALS ═══════════
add wave -noupdate -color Gold $TB/clk_i
add wave -noupdate -color Orange $TB/rst_ni

add wave -noupdate -divider {──── PIPELINE ────}
add wave -noupdate -color Cyan -radix hex $SOC/fe_pc
add wave -noupdate -color Cyan -radix hex $SOC/fe_inst
add wave -noupdate -color Green -radix hex $SOC/pipe1.pc
add wave -noupdate -color Yellow -radix hex $SOC/pipe2.pc
add wave -noupdate -color Magenta -radix hex $SOC/pipe3.pc
add wave -noupdate -color Red -radix hex $SOC/pipe4.pc

add wave -noupdate -divider {──── CONTROL ────}
add wave -noupdate -color Red $SOC/stall_cause
add wave -noupdate -color Orange $SOC/fe_imiss_stall
add wave -noupdate -color Orange $SOC/me_dmiss_stall
add wave -noupdate -color Magenta $SOC/ex_spec_hit
add wave -noupdate -color Red $SOC/trap_active

add wave -noupdate -divider {──── WRITEBACK ────}
add wave -noupdate $SOC/i_writeback/rf_rw_en_o
add wave -noupdate -radix unsigned $SOC/pipe4.rd_addr
add wave -noupdate -radix hex $SOC/i_writeback/wb_data_o

add wave -noupdate -divider {──── REGFILE ────}
add wave -noupdate -radix hex $SOC/i_decode/i_reg_file/registers

run 10000ns
wave zoom full
puts "✅ Minimal debug waveform loaded"
