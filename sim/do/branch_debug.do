##################################################################################
#                     CERES RISC-V — Branch Prediction Debug                    #
##################################################################################
# Focused on: GShare, BTB, RAS, Branch/Jump handling
##################################################################################

################## Hierarchy Paths ##################
set TB        "sim:/tb_wrapper"
set WRAPPER   "$TB/ceres_wrapper"
set SOC       "$WRAPPER/i_soc"
set FETCH     "$SOC/i_fetch"
set GSHARE    "$FETCH/i_gshare_bp"
set RAS       "$GSHARE/i_ras"

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

add wave -noupdate -group "CONTEXT" -color Gold $TB/clk_i
add wave -noupdate -group "CONTEXT" -color Cyan -radix hexadecimal $SOC/fe_pc
add wave -noupdate -group "CONTEXT" -radix hexadecimal $SOC/fe_inst
add wave -noupdate -group "CONTEXT" $SOC/fe_instr_type
add wave -noupdate -group "CONTEXT" -radix hexadecimal $SOC/pipe1.pc
add wave -noupdate -group "CONTEXT" -radix hexadecimal $SOC/pipe2.pc
add wave -noupdate -group "CONTEXT" $SOC/pipe2.instr_type

##################################################################################
#                              SPECULATION OUTCOME                               #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ SPECULATION OUTCOME ═══════════}

add wave -noupdate -group "OUTCOME" -color Green $SOC/ex_spec_hit
add wave -noupdate -group "OUTCOME" -color Red $SOC/ex_pc_sel
add wave -noupdate -group "OUTCOME" -radix hexadecimal $SOC/ex_pc_target
add wave -noupdate -group "OUTCOME" -radix hexadecimal $SOC/ex_pc_target_last

add wave -noupdate -group "OUTCOME" -group "Spec Info" $SOC/fe_spec.taken
add wave -noupdate -group "OUTCOME" -group "Spec Info" $SOC/fe_spec.spectype
add wave -noupdate -group "OUTCOME" -group "Spec Info" -radix hexadecimal $SOC/fe_spec.pc

add wave -noupdate -group "OUTCOME" -group "Pipe2 Spec" $SOC/pipe2.spec.taken
add wave -noupdate -group "OUTCOME" -group "Pipe2 Spec" $SOC/pipe2.spec.spectype
add wave -noupdate -group "OUTCOME" -group "Pipe2 Spec" -radix hexadecimal $SOC/pipe2.spec.pc

##################################################################################
#                              GSHARE PREDICTOR                                  #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ GSHARE PREDICTOR ═══════════}

add wave -noupdate -group "GSHARE" -group "Input" -radix hexadecimal $GSHARE/pc_i
add wave -noupdate -group "GSHARE" -group "Input" -radix hexadecimal $GSHARE/pc_incr_i
add wave -noupdate -group "GSHARE" -group "Input" -radix hexadecimal $GSHARE/inst_i
add wave -noupdate -group "GSHARE" -group "Input" $GSHARE/fetch_valid_i
add wave -noupdate -group "GSHARE" -group "Input" $GSHARE/stall_i
add wave -noupdate -group "GSHARE" -group "Input" $GSHARE/spec_hit_i
add wave -noupdate -group "GSHARE" -group "Input" -radix hexadecimal $GSHARE/pc_target_i

add wave -noupdate -group "GSHARE" -group "Output" $GSHARE/spec_o.taken
add wave -noupdate -group "GSHARE" -group "Output" $GSHARE/spec_o.spectype
add wave -noupdate -group "GSHARE" -group "Output" -radix hexadecimal $GSHARE/spec_o.pc

add wave -noupdate -group "GSHARE" -group "Instruction Decode" $GSHARE/b_type
add wave -noupdate -group "GSHARE" -group "Instruction Decode" $GSHARE/j_type
add wave -noupdate -group "GSHARE" -group "Instruction Decode" $GSHARE/jr_type

add wave -noupdate -group "GSHARE" -group "GHR" -radix binary $GSHARE/ghr
add wave -noupdate -group "GSHARE" -group "GHR" -radix unsigned $GSHARE/pht_idx
add wave -noupdate -group "GSHARE" -group "GHR" -radix unsigned $GSHARE/pht_wr_idx

add wave -noupdate -group "GSHARE" -group "PHT" -radix binary $GSHARE/pht_taken
add wave -noupdate -group "GSHARE" -group "PHT" $GSHARE/pht

add wave -noupdate -group "GSHARE" -group "BTB" $GSHARE/btb_hit
add wave -noupdate -group "GSHARE" -group "BTB" -radix hexadecimal $GSHARE/btb_predicted_target
add wave -noupdate -group "GSHARE" -group "BTB" -radix unsigned $GSHARE/btb_idx
add wave -noupdate -group "GSHARE" -group "BTB" $GSHARE/btb_valid
add wave -noupdate -group "GSHARE" -group "BTB" -radix hexadecimal $GSHARE/btb_tag
add wave -noupdate -group "GSHARE" -group "BTB" -radix hexadecimal $GSHARE/btb_target

add wave -noupdate -group "GSHARE" -group "IBTC" $GSHARE/ibtc_hit
add wave -noupdate -group "GSHARE" -group "IBTC" -radix hexadecimal $GSHARE/ibtc_predicted_target
add wave -noupdate -group "GSHARE" -group "IBTC" $GSHARE/ibtc_valid
add wave -noupdate -group "GSHARE" -group "IBTC" -radix hexadecimal $GSHARE/ibtc_tag
add wave -noupdate -group "GSHARE" -group "IBTC" -radix hexadecimal $GSHARE/ibtc_target

add wave -noupdate -group "GSHARE" -group "EX Feedback" $GSHARE/ex_is_branch
add wave -noupdate -group "GSHARE" -group "EX Feedback" $GSHARE/ex_was_taken
add wave -noupdate -group "GSHARE" -group "EX Feedback" -radix hexadecimal $GSHARE/ex_info_i.pc
add wave -noupdate -group "GSHARE" -group "EX Feedback" $GSHARE/ex_info_i.bjtype

add wave -noupdate -group "GSHARE" -group "All" -radix hexadecimal $GSHARE/*

##################################################################################
#                              RETURN ADDRESS STACK                              #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ RETURN ADDRESS STACK ═══════════}

add wave -noupdate -group "RAS" -group "Control" $RAS/req_valid_i
add wave -noupdate -group "RAS" -group "Control" $RAS/j_type_i
add wave -noupdate -group "RAS" -group "Control" $RAS/jr_type_i
add wave -noupdate -group "RAS" -group "Control" -radix unsigned $RAS/rd_addr_i
add wave -noupdate -group "RAS" -group "Control" -radix unsigned $RAS/r1_addr_i

add wave -noupdate -group "RAS" -group "Push/Pop" -radix hexadecimal $RAS/return_addr_i
add wave -noupdate -group "RAS" -group "Push/Pop" $RAS/popped_o.valid
add wave -noupdate -group "RAS" -group "Push/Pop" -radix hexadecimal $RAS/popped_o.pc

add wave -noupdate -group "RAS" -group "Restore" $RAS/restore_i.valid
add wave -noupdate -group "RAS" -group "Restore" -radix hexadecimal $RAS/restore_i.pc

add wave -noupdate -group "RAS" -group "Stack" -radix unsigned $RAS/tos
add wave -noupdate -group "RAS" -group "Stack" -radix hexadecimal $RAS/stack

add wave -noupdate -group "RAS" -group "All" -radix hexadecimal $RAS/*

##################################################################################
#                              BRANCH TYPES                                      #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ INSTRUCTION TYPES ═══════════}

add wave -noupdate -group "INSTR TYPES" -group "Current" $SOC/fe_instr_type
add wave -noupdate -group "INSTR TYPES" -group "Current" $SOC/pipe1.instr_type
add wave -noupdate -group "INSTR TYPES" -group "Current" $SOC/pipe2.instr_type

add wave -noupdate -group "INSTR TYPES" -group "Branch Control" $SOC/pipe2.pc_sel
add wave -noupdate -group "INSTR TYPES" -group "Branch Control" $SOC/ex_pc_sel

##################################################################################
#                              PC GENERATION                                     #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ PC GENERATION ═══════════}

add wave -noupdate -group "PC GEN" -radix hexadecimal $FETCH/pc_o
add wave -noupdate -group "PC GEN" -radix hexadecimal $FETCH/pc_next
add wave -noupdate -group "PC GEN" -radix hexadecimal $FETCH/pc_incr_o
add wave -noupdate -group "PC GEN" $FETCH/pc_en
add wave -noupdate -group "PC GEN" -radix hexadecimal $FETCH/pc_target_i
add wave -noupdate -group "PC GEN" $FETCH/spec_hit_i

##################################################################################
#                              MISPREDICTION RECOVERY                            #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ MISPREDICTION ═══════════}

add wave -noupdate -group "MISPRED" -color Red $SOC/ex_spec_hit
add wave -noupdate -group "MISPRED" -radix hexadecimal $SOC/ex_pc_target_last
add wave -noupdate -group "MISPRED" $SOC/de_flush
add wave -noupdate -group "MISPRED" $SOC/ex_flush
add wave -noupdate -group "MISPRED" $SOC/priority_flush

##################################################################################
#                              STATISTICS (Conceptual)                           #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ DEBUG INFO ═══════════}

add wave -noupdate -group "DEBUG" $SOC/stall_cause
add wave -noupdate -group "DEBUG" $SOC/fe_imiss_stall

##################################################################################
#                              RUN SIMULATION                                    #
##################################################################################
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ns} 0}
configure wave -timelineunits ns
run 10000ns
wave zoom full

puts "═══════════════════════════════════════════════════════════════════"
puts "  CERES Branch Prediction Debug Waveform Loaded!"
puts "═══════════════════════════════════════════════════════════════════"
