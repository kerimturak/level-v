##################################################################################
#                     CERES RISC-V — Exception Debug Waveform                   #
##################################################################################
# Focused on: Exceptions, Traps, CSRs, Interrupt handling
##################################################################################

################## Hierarchy Paths ##################
set TB        "sim:/tb_wrapper"
set WRAPPER   "$TB/ceres_wrapper"
set SOC       "$WRAPPER/i_soc"
set FETCH     "$SOC/i_fetch"
set DECODE    "$SOC/i_decode"
set EXECUTE   "$SOC/i_execution"
set MEMORY    "$SOC/i_memory"
set CSR       "$EXECUTE/i_cs_reg_file"

################## Wave Configuration ##################
configure wave -namecolwidth 350
configure wave -valuecolwidth 150
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -timelineunits ns

##################################################################################
#                              PIPELINE CONTEXT                                  #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ PIPELINE CONTEXT ═══════════}

add wave -noupdate -group "PIPELINE" -color Gold $TB/clk_i
add wave -noupdate -group "PIPELINE" -color Cyan -radix hexadecimal $SOC/fe_pc
add wave -noupdate -group "PIPELINE" -color Cyan -radix hexadecimal $SOC/fe_inst
add wave -noupdate -group "PIPELINE" -color Green -radix hexadecimal $SOC/pipe1.pc
add wave -noupdate -group "PIPELINE" -color Yellow -radix hexadecimal $SOC/pipe2.pc
add wave -noupdate -group "PIPELINE" -color Magenta -radix hexadecimal $SOC/pipe3.pc
add wave -noupdate -group "PIPELINE" -color Red -radix hexadecimal $SOC/pipe4.pc

add wave -noupdate -group "PIPELINE" $SOC/pipe1.instr_type
add wave -noupdate -group "PIPELINE" $SOC/pipe2.instr_type

##################################################################################
#                              EXCEPTION SOURCES                                 #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ EXCEPTION SOURCES ═══════════}

add wave -noupdate -group "EXC SOURCES" -group "Fetch" -color Orange $SOC/fe_exc_type
add wave -noupdate -group "EXC SOURCES" -group "Fetch" -color Orange $SOC/fe_active_exc_type
add wave -noupdate -group "EXC SOURCES" -group "Fetch" $FETCH/illegal_instr
add wave -noupdate -group "EXC SOURCES" -group "Fetch" $FETCH/i_pma/grand_o

add wave -noupdate -group "EXC SOURCES" -group "Decode" -color Yellow $SOC/de_exc_type
add wave -noupdate -group "EXC SOURCES" -group "Decode" -color Yellow $SOC/de_active_exc_type
add wave -noupdate -group "EXC SOURCES" -group "Decode" $DECODE/exc_type_o

add wave -noupdate -group "EXC SOURCES" -group "Execute" -color Red $SOC/ex_exc_type
add wave -noupdate -group "EXC SOURCES" -group "Execute" -color Red $SOC/ex_alu_exc_type
add wave -noupdate -group "EXC SOURCES" -group "Execute" $EXECUTE/exc_type_o

##################################################################################
#                              TRAP HANDLING                                     #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ TRAP HANDLING ═══════════}

add wave -noupdate -group "TRAP" -group "Active" -color Red $SOC/trap_active
add wave -noupdate -group "TRAP" -group "Active" -color Red $SOC/fe_trap_active
add wave -noupdate -group "TRAP" -group "Active" -color Red $SOC/de_trap_active

add wave -noupdate -group "TRAP" -group "Cause & Value" -radix hexadecimal $SOC/ex_trap_cause
add wave -noupdate -group "TRAP" -group "Cause & Value" -radix hexadecimal $SOC/ex_trap_mepc
add wave -noupdate -group "TRAP" -group "Cause & Value" -radix hexadecimal $SOC/trap_tval

add wave -noupdate -group "TRAP" -group "Priority" $SOC/excp_mask
add wave -noupdate -group "TRAP" -group "Priority" $SOC/priority_flush

add wave -noupdate -group "TRAP" -group "Target" -radix hexadecimal $SOC/ex_mtvec
add wave -noupdate -group "TRAP" -group "Target" -radix hexadecimal $SOC/ex_pc_target_last

##################################################################################
#                              CSR REGISTERS                                     #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ CSR REGISTERS ═══════════}

add wave -noupdate -group "CSR ACCESS" -group "Control" $CSR/rd_en_i
add wave -noupdate -group "CSR ACCESS" -group "Control" $CSR/wr_en_i
add wave -noupdate -group "CSR ACCESS" -group "Control" -radix hexadecimal $CSR/csr_idx_i
add wave -noupdate -group "CSR ACCESS" -group "Control" -radix hexadecimal $CSR/csr_wdata_i
add wave -noupdate -group "CSR ACCESS" -group "Control" -radix hexadecimal $CSR/csr_rdata_o

add wave -noupdate -group "CSR ACCESS" -group "Trap Interface" $CSR/trap_active_i
add wave -noupdate -group "CSR ACCESS" -group "Trap Interface" -radix hexadecimal $CSR/trap_cause_i
add wave -noupdate -group "CSR ACCESS" -group "Trap Interface" -radix hexadecimal $CSR/trap_mepc_i
add wave -noupdate -group "CSR ACCESS" -group "Trap Interface" -radix hexadecimal $CSR/trap_tval_i

add wave -noupdate -group "CSR REGS" -group "Machine Status" -radix hexadecimal $CSR/mstatus_q
add wave -noupdate -group "CSR REGS" -group "Machine Status" $CSR/mstatus_q.mie
add wave -noupdate -group "CSR REGS" -group "Machine Status" $CSR/mstatus_q.mpie
add wave -noupdate -group "CSR REGS" -group "Machine Status" $CSR/mstatus_q.mpp

add wave -noupdate -group "CSR REGS" -group "Trap Setup" -radix hexadecimal $CSR/mtvec_o
add wave -noupdate -group "CSR REGS" -group "Trap Setup" -radix hexadecimal $CSR/mie_q
add wave -noupdate -group "CSR REGS" -group "Trap Setup" -radix hexadecimal $CSR/mip_q

add wave -noupdate -group "CSR REGS" -group "Trap Handling" -radix hexadecimal $CSR/mepc_o
add wave -noupdate -group "CSR REGS" -group "Trap Handling" -radix hexadecimal $CSR/mcause_q
add wave -noupdate -group "CSR REGS" -group "Trap Handling" -radix hexadecimal $CSR/mtval_q

add wave -noupdate -group "CSR REGS" -group "Counters" -radix unsigned $CSR/mcycle_q
add wave -noupdate -group "CSR REGS" -group "Counters" -radix unsigned $CSR/minstret_q

add wave -noupdate -group "CSR REGS" -group "All" -radix hexadecimal $CSR/*

##################################################################################
#                              MRET / ECALL / EBREAK                             #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ SPECIAL INSTRUCTIONS ═══════════}

add wave -noupdate -group "SPECIAL INSTR" $SOC/pipe2.instr_type
add wave -noupdate -group "SPECIAL INSTR" -radix hexadecimal $SOC/pipe2.pc

# MRET specific
add wave -noupdate -group "MRET" -radix hexadecimal $CSR/mepc_o
add wave -noupdate -group "MRET" $CSR/mstatus_q.mpie
add wave -noupdate -group "MRET" $CSR/mstatus_q.mpp

##################################################################################
#                              FLUSH SIGNALS                                     #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ FLUSH CONTROL ═══════════}

add wave -noupdate -group "FLUSH" -color Magenta $SOC/de_flush
add wave -noupdate -group "FLUSH" -color Magenta $SOC/de_flush_en
add wave -noupdate -group "FLUSH" -color Magenta $SOC/ex_flush
add wave -noupdate -group "FLUSH" -color Magenta $SOC/ex_flush_en
add wave -noupdate -group "FLUSH" -color Red $SOC/fencei_flush
add wave -noupdate -group "FLUSH" -color Red -radix hexadecimal $SOC/flush_pc

##################################################################################
#                              STALL SIGNALS                                     #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ STALL CONTROL ═══════════}

add wave -noupdate -group "STALL" -color Red $SOC/stall_cause
add wave -noupdate -group "STALL" $SOC/fe_stall
add wave -noupdate -group "STALL" $SOC/de_stall
add wave -noupdate -group "STALL" $SOC/fe_imiss_stall
add wave -noupdate -group "STALL" $SOC/me_dmiss_stall
add wave -noupdate -group "STALL" $SOC/ex_alu_stall
add wave -noupdate -group "STALL" $SOC/me_fencei_stall

##################################################################################
#                              RUN SIMULATION                                    #
##################################################################################
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ns} 0}
configure wave -timelineunits ns
run 10000ns
wave zoom full

puts "═══════════════════════════════════════════════════════════════════"
puts "  CERES Exception Debug Waveform Loaded!"
puts "═══════════════════════════════════════════════════════════════════"
