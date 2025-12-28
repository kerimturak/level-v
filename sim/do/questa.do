##################################################################################
#                     CERES RISC-V - Debug Waveform                            #
#                        Questa Simulation Script                              #
##################################################################################
# Features:
#   - Hierarchical grouping by module
#   - Input/Output separation for each module
#   - Automatic radix selection (hex/decimal/binary)
#   - Collapsible groups for easy navigation
##################################################################################

################## Global Settings ##################
set WildcardFilter [lsearch -not -all -inline $WildcardFilter Memory]
set WildcardFilter [lsearch -not -all -inline $WildcardFilter Nets]
set WildcardFilter [lsearch -not -all -inline $WildcardFilter Variable]
set WildcardFilter [lsearch -not -all -inline $WildcardFilter Constant]
set WildcardFilter [lsearch -not -all -inline $WildcardFilter Parameter]
set WildcardFilter [lsearch -not -all -inline $WildcardFilter SpecParam]
set WildcardFilter [lsearch -not -all -inline $WildcardFilter Generic]

set WildcardSizeThreshold 163840
configure wave -namecolwidth 250
configure wave -valuecolwidth 50
configure wave -justifyvalue left
configure wave -signalnamewidth 1


################## Hierarchy Paths ##################
set TB            "/tb_wrapper"
set WRAPPER       "$TB/ceres_wrapper"
set CPU           "$WRAPPER/i_soc"
set FETCH         "$CPU/i_fetch"
set DECODE        "$CPU/i_decode"
set EXECUTE       "$CPU/i_execution"
set MEMORY        "$CPU/i_memory"
set WRITEBACK     "$CPU/i_writeback"
set HAZARD        "$CPU/i_hazard_unit"
set ARBITER       "$CPU/i_memory_arbiter"

# Fetch submodules
set ICACHE        "$FETCH/i_icache"
set ALIGN_BUFFER  "$FETCH/i_align_buffer"
set COMP_DECODER  "$FETCH/i_compressed_decoder"
set GSHARE        "$FETCH/i_gshare_bp"
set RAS           "$GSHARE/i_ras"
set IPMA          "$FETCH/i_pma"

# Decode submodules
set CTRL_UNIT     "$DECODE/i_control_unit"
set REG_FILE      "$DECODE/i_reg_file"
set EXTEND        "$DECODE/i_extend"

# Execute submodules
set ALU           "$EXECUTE/i_alu"
set CSR_FILE      "$EXECUTE/i_cs_reg_file"

# Memory submodules
set DCACHE        "$MEMORY/i_dcache"
set DPMA          "$MEMORY/i_dpma"

# Wrapper submodules
set MAIN_RAM      "$WRAPPER/i_main_ram"
set UART          "$WRAPPER/i_uart"
set UART_TX       "$UART/i_uart_tx"
set UART_RX       "$UART/i_uart_rx"

# Wishbone Bus submodules
set WB_MASTER     "$WRAPPER/i_wb_master"
set WB_INTERCON   "$WRAPPER/i_wb_interconnect"
set WB_CLINT      "$WRAPPER/i_wb_clint"
set WB_PBUS       "$WRAPPER/i_wb_pbus"


add wave -position insertpoint -radix hexadecimal -group "WRAPPER"  sim:$REG_FILE/registers
add wave -position insertpoint -radix hexadecimal -group "WRAPPER"  -group "uart_tx_fifo" sim:$UART_TX/i_tx_buffer/*

add wave -position insertpoint -radix hexadecimal -group "WRAPPER"  -group "CSR" sim:$CSR_FILE/*

################## Wrapper ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group in       sim:$WRAPPER/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group out      sim:$WRAPPER/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group internal sim:$WRAPPER/*

################## Soc ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC" -group in       sim:$CPU/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC" -group out      sim:$CPU/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC" -group internal sim:$CPU/*
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "FETCH1" 		-group internal sim:$FETCH/*
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "DECODE2" 		-group internal sim:$DECODE/*
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "EXECUTION3" 	-group internal sim:$EXECUTE/*
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "MEMORY4" 		-group internal sim:$MEMORY/*
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "WRITEBACK5" 	-group internal sim:$WRITEBACK/*

################## FETCH ##################
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "WRAPPER" -group "SOC" -group "FETCH1" -group internal sim:$FETCH/*
		################## GSHARE ##################
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC" -group "FETCH1" -group "BP"     -group internal  sim:$GSHARE/*
				################## RAS ##################
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC" -group "FETCH1" -group "BP"  -group "RAS"  -group internal   sim:$RAS/*
		################## IPMA ##################
add wave -position insertpoint -radix hexadecimal  					-group "WRAPPER" -group "SOC" -group "FETCH1" -group "IPMA"               sim:$IPMA/*
		################## ALIGN BUFFER ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC" -group "FETCH1" -group "ALIGN BUFFER" -group in       sim:$ALIGN_BUFFER/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC" -group "FETCH1" -group "ALIGN BUFFER" -group out      sim:$ALIGN_BUFFER/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC" -group "FETCH1" -group "ALIGN BUFFER" -group internal sim:$ALIGN_BUFFER/*
		################## ICACHE TOP ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC" -group "FETCH1" -group in       sim:$ICACHE/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC" -group "FETCH1" -group out      sim:$ICACHE/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC" -group "FETCH1" -group internal sim:$ICACHE/*
		################## COMPRESSED DECODER ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC" -group "FETCH1" -group "COMP DECODER" -group in       sim:$COMP_DECODER/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC" -group "FETCH1" -group "COMP DECODER" -group out      sim:$COMP_DECODER/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC" -group "FETCH1" -group "COMP DECODER" -group internal sim:$COMP_DECODER/*

################## DECODE ##################
		################## CONTROL UNIT ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC"  -group "DECODE2" -group "CONTROL UNIT" -group in       sim:$CTRL_UNIT/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC"  -group "DECODE2" -group "CONTROL UNIT" -group out      sim:$CTRL_UNIT/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC"  -group "DECODE2" -group "CONTROL UNIT" -group internal sim:$CTRL_UNIT/*
		################## REG FILE ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC"  -group "DECODE2" -group "REG FILE" -group in       sim:$REG_FILE/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC"  -group "DECODE2" -group "REG FILE" -group out      sim:$REG_FILE/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC"  -group "DECODE2" -group "REG FILE" -group internal sim:$REG_FILE/*
		################## EXTEND ##################
add wave -position insertpoint -radix hexadecimal        -group "WRAPPER" -group "SOC"  -group "DECODE2" -group "EXTEND" -group in       sim:$EXTEND/*

################## EXECUTE ##################
	################## ALU ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC"  -group "EXECUTION3" -group "ALU" -group in       sim:$ALU/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC"  -group "EXECUTION3" -group "ALU" -group out      sim:$ALU/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC"  -group "EXECUTION3" -group "ALU" -group internal sim:$ALU/*
	################## CS_RF ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC"  -group "EXECUTION3" -group "CSR" -group in       sim:$CSR_FILE/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC"  -group "EXECUTION3" -group "CSR" -group out      sim:$CSR_FILE/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC"  -group "EXECUTION3" -group "CSR" -group internal sim:$CSR_FILE/*

################## MEMORY ##################
	################## DCACHE ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC"  -group "MEMORY4" -group "DCACHE" -group in       sim:$DCACHE/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC"  -group "MEMORY4" -group "DCACHE" -group out      sim:$DCACHE/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC"  -group "MEMORY4" -group "DCACHE" -group internal sim:$DCACHE/*
#add wave -position insertpoint -radix hexadecimal           -group "WRAPPER" -group "SOC"  -group "MEMORY4" -group "DPMA"                   sim:$DPMA/*

################## MAIN MEMORY ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "MAIN MEMORY" -group in       sim:$MAIN_RAM/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "MAIN MEMORY" -group out      sim:$MAIN_RAM/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "MAIN MEMORY" -group internal sim:$MAIN_RAM/*
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "UART" sim:$UART/*






################## UART ##################
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "MEMORY4" -group "UART"   sim:$UART/*
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "MEMORY4" -group "UART"  -group "UART_TX" sim:$UART_TX/*
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "MEMORY4" -group "UART"  -group "UART_RX" sim:$UART_RX/*

################## ARBITER ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC"  -group "ARBITER" -group in       sim:$ARBITER/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC"  -group "ARBITER" -group out      sim:$ARBITER/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC"  -group "ARBITER" -group internal sim:$ARBITER/*

################## HAZARD ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC"  -group "HAZARD" -group in       sim:$HAZARD/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC"  -group "HAZARD" -group out      sim:$HAZARD/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC"  -group "HAZARD" -group internal sim:$HAZARD/*




##################################################################################
#                              QUICK DEBUG VIEW                                  #
##################################################################################
add wave -noupdate -divider -height 20 {=============== QUICK DEBUG ===============}

add wave -noupdate -group "QUICK_DEBUG" -group "Clock/Reset" -color Gold $TB/clk_i
add wave -noupdate -group "QUICK_DEBUG" -group "Clock/Reset" -color Orange $TB/rst_ni

add wave -noupdate -group "QUICK_DEBUG" -group "PC Progress" -color Cyan -radix hexadecimal $CPU/fe_pc
add wave -noupdate -group "QUICK_DEBUG" -group "PC Progress" -color Green -radix hexadecimal $CPU/pipe1.pc
add wave -noupdate -group "QUICK_DEBUG" -group "PC Progress" -color Yellow -radix hexadecimal $CPU/pipe2.pc
add wave -noupdate -group "QUICK_DEBUG" -group "PC Progress" -color Magenta -radix hexadecimal $CPU/pipe3.pc
add wave -noupdate -group "QUICK_DEBUG" -group "PC Progress" -color Red -radix hexadecimal $CPU/pipe4.pc

add wave -noupdate -group "QUICK_DEBUG" -group "Instructions" -radix hexadecimal $CPU/fe_inst
add wave -noupdate -group "QUICK_DEBUG" -group "Instructions" -radix hexadecimal $CPU/pipe1.inst
add wave -noupdate -group "QUICK_DEBUG" -group "Instructions" $CPU/fe_instr_type
add wave -noupdate -group "QUICK_DEBUG" -group "Instructions" $CPU/pipe1.instr_type
add wave -noupdate -group "QUICK_DEBUG" -group "Instructions" $CPU/pipe2.instr_type

add wave -noupdate -group "QUICK_DEBUG" -group "Stalls" -color Red $CPU/stall_cause
add wave -noupdate -group "QUICK_DEBUG" -group "Stalls" -color Orange $CPU/fe_imiss_stall
add wave -noupdate -group "QUICK_DEBUG" -group "Stalls" -color Orange $CPU/me_dmiss_stall
add wave -noupdate -group "QUICK_DEBUG" -group "Stalls" -color Orange $CPU/ex_alu_stall

add wave -noupdate -group "QUICK_DEBUG" -group "Exceptions" -color Red $CPU/trap_active
add wave -noupdate -group "QUICK_DEBUG" -group "Exceptions" $CPU/excp_mask
add wave -noupdate -group "QUICK_DEBUG" -group "Exceptions" $CPU/priority_flush

add wave -noupdate -group "QUICK_DEBUG" -group "Register File" -radix hexadecimal $REG_FILE/registers


add wave -noupdate -group "QUICK_DEBUG" -group "Inputs" -color Gold $CPU/clk_i
add wave -noupdate -group "QUICK_DEBUG" -group "Inputs" -color Orange $CPU/rst_ni
add wave -noupdate -group "QUICK_DEBUG" -group "Inputs" -radix hexadecimal $CPU/iomem_res_i

add wave -noupdate -group "QUICK_DEBUG" -group "Outputs" -radix hexadecimal $CPU/iomem_req_o

add wave -noupdate -group "QUICK_DEBUG" -group "Pipeline Registers" -radix hexadecimal $CPU/pipe1
add wave -noupdate -group "QUICK_DEBUG" -group "Pipeline Registers" -radix hexadecimal $CPU/pipe2
add wave -noupdate -group "QUICK_DEBUG" -group "Pipeline Registers" -radix hexadecimal $CPU/pipe3
add wave -noupdate -group "QUICK_DEBUG" -group "Pipeline Registers" -radix hexadecimal $CPU/pipe4

add wave -noupdate -group "QUICK_DEBUG" -group "Stall/Flush Control" $CPU/stall_cause
add wave -noupdate -group "QUICK_DEBUG" -group "Stall/Flush Control" $CPU/fe_imiss_stall
add wave -noupdate -group "QUICK_DEBUG" -group "Stall/Flush Control" $CPU/me_dmiss_stall
add wave -noupdate -group "QUICK_DEBUG" -group "Stall/Flush Control" $CPU/ex_alu_stall
add wave -noupdate -group "QUICK_DEBUG" -group "Stall/Flush Control" $CPU/me_fencei_stall
add wave -noupdate -group "QUICK_DEBUG" -group "Stall/Flush Control" $CPU/de_flush
add wave -noupdate -group "QUICK_DEBUG" -group "Stall/Flush Control" $CPU/ex_flush
add wave -noupdate -group "QUICK_DEBUG" -group "Stall/Flush Control" $CPU/fencei_flush
add wave -noupdate -group "QUICK_DEBUG" -group "Stall/Flush Control" $CPU/priority_flush

add wave -noupdate -group "QUICK_DEBUG" -group "Exception Handling" $CPU/trap_active
add wave -noupdate -group "QUICK_DEBUG" -group "Exception Handling" $CPU/fe_trap_active
add wave -noupdate -group "QUICK_DEBUG" -group "Exception Handling" $CPU/de_trap_active
add wave -noupdate -group "QUICK_DEBUG" -group "Exception Handling" $CPU/excp_mask
add wave -noupdate -group "QUICK_DEBUG" -group "Exception Handling" -radix hexadecimal $CPU/trap_tval
add wave -noupdate -group "QUICK_DEBUG" -group "Exception Handling" $CPU/fe_exc_type
add wave -noupdate -group "QUICK_DEBUG" -group "Exception Handling" $CPU/de_exc_type
add wave -noupdate -group "QUICK_DEBUG" -group "Exception Handling" $CPU/ex_exc_type
add wave -noupdate -group "QUICK_DEBUG" -group "Exception Handling" $CPU/ex_alu_exc_type
add wave -noupdate -group "QUICK_DEBUG" -group "Exception Handling" -radix hexadecimal $CPU/ex_trap_cause
add wave -noupdate -group "QUICK_DEBUG" -group "Exception Handling" -radix hexadecimal $CPU/ex_trap_mepc
add wave -noupdate -group "QUICK_DEBUG" -group "Exception Handling" -radix hexadecimal $CPU/ex_mtvec

add wave -noupdate -group "QUICK_DEBUG" -group "Branch Prediction" $CPU/ex_spec_hit
add wave -noupdate -group "QUICK_DEBUG" -group "Branch Prediction" $CPU/ex_pc_sel
add wave -noupdate -group "QUICK_DEBUG" -group "Branch Prediction" -radix hexadecimal $CPU/ex_pc_target
add wave -noupdate -group "QUICK_DEBUG" -group "Branch Prediction" -radix hexadecimal $CPU/ex_pc_target_last
add wave -noupdate -group "QUICK_DEBUG" -group "Branch Prediction" $CPU/fe_spec

add wave -noupdate -group "QUICK_DEBUG" -group "Data Request" -radix hexadecimal $CPU/ex_data_req
add wave -noupdate -group "QUICK_DEBUG" -group "Data Request" -radix hexadecimal $CPU/me_data_req

add wave -noupdate -group "QUICK_DEBUG" -group "Forwarding" $CPU/de_fwd_a
add wave -noupdate -group "QUICK_DEBUG" -group "Forwarding" $CPU/de_fwd_b
add wave -noupdate -group "QUICK_DEBUG" -group "Forwarding" $CPU/ex_fwd_a
add wave -noupdate -group "QUICK_DEBUG" -group "Forwarding" $CPU/ex_fwd_b



add wave -position insertpoint -radix hexadecimal -group "WRAPPER" -group "WB_MASTER" sim:$WB_MASTER/*
add wave -position insertpoint -radix hexadecimal -group "WRAPPER" -group "WB_INTERCON" sim:$WB_INTERCON/*
add wave -position insertpoint -radix hexadecimal -group "WRAPPER" -group "WB_CLINT" sim:$WB_CLINT/*
add wave -position insertpoint -radix hexadecimal -group "WRAPPER" -group "WB_PBUS" sim:$WB_PBUS/*

run 10000ns
wave zoom full