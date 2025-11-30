##################################################################################
#                     CERES RISC-V — Hazard & Forwarding Debug                  #
##################################################################################
# Focused on: Data hazards, RAW dependencies, forwarding paths
##################################################################################

################## Hierarchy Paths ##################
set TB        "sim:/tb_wrapper"
set WRAPPER   "$TB/ceres_wrapper"
set SOC       "$WRAPPER/i_soc"
set DECODE    "$SOC/i_decode"
set EXECUTE   "$SOC/i_execution"
set HAZARD    "$SOC/i_hazard_unit"

################## Wave Configuration ##################
configure wave -namecolwidth 350
configure wave -valuecolwidth 150
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -timelineunits ns

##################################################################################
#                              PIPELINE REGISTERS                                #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ PIPELINE STATE ═══════════}

add wave -noupdate -group "PIPELINE" -color Gold $TB/clk_i
add wave -noupdate -group "PIPELINE" -radix hex $SOC/fe_pc
add wave -noupdate -group "PIPELINE" -radix hex $SOC/fe_inst

add wave -noupdate -group "PIPELINE" -group "DE Stage" -radix hex $SOC/pipe1.pc
add wave -noupdate -group "PIPELINE" -group "DE Stage" -radix hex $SOC/pipe1.inst
add wave -noupdate -group "PIPELINE" -group "DE Stage" -radix unsigned $SOC/pipe1.inst.r1_addr
add wave -noupdate -group "PIPELINE" -group "DE Stage" -radix unsigned $SOC/pipe1.inst.r2_addr
add wave -noupdate -group "PIPELINE" -group "DE Stage" -radix unsigned $SOC/pipe1.inst.rd_addr

add wave -noupdate -group "PIPELINE" -group "EX Stage" -radix hex $SOC/pipe2.pc
add wave -noupdate -group "PIPELINE" -group "EX Stage" $SOC/pipe2.instr_type
add wave -noupdate -group "PIPELINE" -group "EX Stage" -radix unsigned $SOC/pipe2.r1_addr
add wave -noupdate -group "PIPELINE" -group "EX Stage" -radix unsigned $SOC/pipe2.r2_addr
add wave -noupdate -group "PIPELINE" -group "EX Stage" -radix unsigned $SOC/pipe2.rd_addr
add wave -noupdate -group "PIPELINE" -group "EX Stage" $SOC/pipe2.rf_rw_en

add wave -noupdate -group "PIPELINE" -group "ME Stage" -radix hex $SOC/pipe3.pc
add wave -noupdate -group "PIPELINE" -group "ME Stage" -radix unsigned $SOC/pipe3.rd_addr
add wave -noupdate -group "PIPELINE" -group "ME Stage" $SOC/pipe3.rf_rw_en
add wave -noupdate -group "PIPELINE" -group "ME Stage" -radix hex $SOC/pipe3.alu_result

add wave -noupdate -group "PIPELINE" -group "WB Stage" -radix hex $SOC/pipe4.pc
add wave -noupdate -group "PIPELINE" -group "WB Stage" -radix unsigned $SOC/pipe4.rd_addr
add wave -noupdate -group "PIPELINE" -group "WB Stage" $SOC/pipe4.rf_rw_en
add wave -noupdate -group "PIPELINE" -group "WB Stage" -radix hex $SOC/pipe4.alu_result

##################################################################################
#                              HAZARD UNIT                                       #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ HAZARD UNIT ═══════════}

add wave -noupdate -group "HAZARD" -group "Input Addresses" -radix unsigned $HAZARD/r1_addr_de_i
add wave -noupdate -group "HAZARD" -group "Input Addresses" -radix unsigned $HAZARD/r2_addr_de_i
add wave -noupdate -group "HAZARD" -group "Input Addresses" -radix unsigned $HAZARD/r1_addr_ex_i
add wave -noupdate -group "HAZARD" -group "Input Addresses" -radix unsigned $HAZARD/r2_addr_ex_i
add wave -noupdate -group "HAZARD" -group "Input Addresses" -radix unsigned $HAZARD/rd_addr_ex_i
add wave -noupdate -group "HAZARD" -group "Input Addresses" -radix unsigned $HAZARD/rd_addr_me_i
add wave -noupdate -group "HAZARD" -group "Input Addresses" -radix unsigned $HAZARD/rd_addr_wb_i

add wave -noupdate -group "HAZARD" -group "RF Write Enable" $HAZARD/rf_rw_me_i
add wave -noupdate -group "HAZARD" -group "RF Write Enable" $HAZARD/rf_rw_wb_i

add wave -noupdate -group "HAZARD" -group "Stall Outputs" -color Red $HAZARD/stall_fe_o
add wave -noupdate -group "HAZARD" -group "Stall Outputs" -color Red $HAZARD/stall_de_o

add wave -noupdate -group "HAZARD" -group "Flush Outputs" -color Magenta $HAZARD/flush_de_o
add wave -noupdate -group "HAZARD" -group "Flush Outputs" -color Magenta $HAZARD/flush_ex_o

add wave -noupdate -group "HAZARD" -group "EX Forwarding" -color Green $HAZARD/fwd_a_ex_o
add wave -noupdate -group "HAZARD" -group "EX Forwarding" -color Green $HAZARD/fwd_b_ex_o

add wave -noupdate -group "HAZARD" -group "DE Forwarding" -color Cyan $HAZARD/fwd_a_de_o
add wave -noupdate -group "HAZARD" -group "DE Forwarding" -color Cyan $HAZARD/fwd_b_de_o

add wave -noupdate -group "HAZARD" -group "Control" $HAZARD/pc_sel_ex_i
add wave -noupdate -group "HAZARD" -group "Control" $HAZARD/rslt_sel_ex_0

add wave -noupdate -group "HAZARD" -group "All" -radix hex $HAZARD/*

##################################################################################
#                              FORWARDING PATHS                                  #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ FORWARDING DATA ═══════════}

add wave -noupdate -group "FWD DATA" -group "Decode Stage" -radix hex $DECODE/r1_data
add wave -noupdate -group "FWD DATA" -group "Decode Stage" -radix hex $DECODE/r2_data
add wave -noupdate -group "FWD DATA" -group "Decode Stage" -radix hex $DECODE/r1_data_o
add wave -noupdate -group "FWD DATA" -group "Decode Stage" -radix hex $DECODE/r2_data_o
add wave -noupdate -group "FWD DATA" -group "Decode Stage" $DECODE/fwd_a_i
add wave -noupdate -group "FWD DATA" -group "Decode Stage" $DECODE/fwd_b_i
add wave -noupdate -group "FWD DATA" -group "Decode Stage" -radix hex $DECODE/wb_data_i

add wave -noupdate -group "FWD DATA" -group "Execute Stage" -radix hex $SOC/pipe2.r1_data
add wave -noupdate -group "FWD DATA" -group "Execute Stage" -radix hex $SOC/pipe2.r2_data
add wave -noupdate -group "FWD DATA" -group "Execute Stage" $SOC/ex_fwd_a
add wave -noupdate -group "FWD DATA" -group "Execute Stage" $SOC/ex_fwd_b

add wave -noupdate -group "FWD DATA" -group "Forward Sources" -radix hex $SOC/pipe3.alu_result
add wave -noupdate -group "FWD DATA" -group "Forward Sources" -radix hex $SOC/wb_data

##################################################################################
#                              ALU OPERANDS                                      #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ ALU OPERANDS ═══════════}

add wave -noupdate -group "ALU OPS" -radix hex $EXECUTE/i_alu/alu_a_i
add wave -noupdate -group "ALU OPS" -radix hex $EXECUTE/i_alu/alu_b_i
add wave -noupdate -group "ALU OPS" $EXECUTE/i_alu/op_sel_i
add wave -noupdate -group "ALU OPS" -radix hex $EXECUTE/i_alu/alu_o

add wave -noupdate -group "ALU OPS" -group "Operand Select" $SOC/pipe2.alu_in1_sel
add wave -noupdate -group "ALU OPS" -group "Operand Select" $SOC/pipe2.alu_in2_sel
add wave -noupdate -group "ALU OPS" -group "Operand Select" -radix hex $SOC/pipe2.imm

##################################################################################
#                              STALL ANALYSIS                                    #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ STALL ANALYSIS ═══════════}

add wave -noupdate -group "STALLS" -color Red $SOC/stall_cause
add wave -noupdate -group "STALLS" $SOC/fe_stall
add wave -noupdate -group "STALLS" $SOC/de_stall
add wave -noupdate -group "STALLS" $SOC/fe_imiss_stall
add wave -noupdate -group "STALLS" $SOC/me_dmiss_stall
add wave -noupdate -group "STALLS" $SOC/ex_alu_stall
add wave -noupdate -group "STALLS" $SOC/me_fencei_stall

add wave -noupdate -group "STALLS" -group "Enable Signals" $SOC/de_enable
add wave -noupdate -group "STALLS" -group "Enable Signals" $SOC/de_flush_en
add wave -noupdate -group "STALLS" -group "Enable Signals" $SOC/ex_flush_en

##################################################################################
#                              REGISTER FILE                                     #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ REGISTER FILE ═══════════}

add wave -noupdate -group "REGFILE" -group "Write Port" $DECODE/i_reg_file/rw_en_i
add wave -noupdate -group "REGFILE" -group "Write Port" -radix unsigned $DECODE/i_reg_file/waddr_i
add wave -noupdate -group "REGFILE" -group "Write Port" -radix hex $DECODE/i_reg_file/wdata_i

add wave -noupdate -group "REGFILE" -group "Read Port 1" -radix unsigned $DECODE/i_reg_file/r1_addr_i
add wave -noupdate -group "REGFILE" -group "Read Port 1" -radix hex $DECODE/i_reg_file/r1_data_o

add wave -noupdate -group "REGFILE" -group "Read Port 2" -radix unsigned $DECODE/i_reg_file/r2_addr_i
add wave -noupdate -group "REGFILE" -group "Read Port 2" -radix hex $DECODE/i_reg_file/r2_data_o

add wave -noupdate -group "REGFILE" -group "All Registers" -radix hex $DECODE/i_reg_file/registers

##################################################################################
#                              RUN SIMULATION                                    #
##################################################################################
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ns} 0}
configure wave -timelineunits ns
run 10000ns
wave zoom full

puts "═══════════════════════════════════════════════════════════════════"
puts "  CERES Hazard & Forwarding Debug Waveform Loaded!"
puts "═══════════════════════════════════════════════════════════════════"
