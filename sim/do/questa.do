################## Settings ##################

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

add wave -position insertpoint -radix hexadecimal -group "WRAPPER"  sim:/tb_wrapper/ceres_wrapper/i_soc/i_decode/i_reg_file/registers
add wave -position insertpoint -radix hexadecimal -group "WRAPPER" -group "UART_TX_BUFFER" sim:/tb_wrapper/ceres_wrapper/i_soc/i_memory/uart_inst/uart_tx/tx_buffer/*

add wave -position insertpoint -radix hexadecimal -group "WRAPPER"  -group "CSR" sim:/tb_wrapper/ceres_wrapper/i_soc/execution/u_cs_reg_file/*

################## Wrapper ##################
add wave -position insertpoint -radix hexadecimal        -group "WRAPPER" -group in       sim:/tb_wrapper/*


################## SOC ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC" -group in       sim:/tb_wrapper/ceres_wrapper/i_soc/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC" -group out      sim:/tb_wrapper/ceres_wrapper/i_soc/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC" -group internal sim:/tb_wrapper/ceres_wrapper/i_soc/*

add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "FETCH1" -group internal sim:/tb_wrapper/ceres_wrapper/i_soc/fetch/*
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "DECODE2" -group internal sim:/tb_wrapper/ceres_wrapper/i_soc/i_decode/*
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "EXECUTION3" -group internal sim:/tb_wrapper/ceres_wrapper/i_soc/execution/*
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "MEMORY4" -group internal sim:/tb_wrapper/ceres_wrapper/i_soc/i_memory/*
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "WRITEBACK5" -group internal sim:/tb_wrapper/ceres_wrapper/i_soc/writeback/*

################## BRANCH PREDICTION ##################
add wave -position insertpoint  \
-radix hexadecimal          -group "WRAPPER" -group "SOC"  -group "FETCH1" -group "BRANCH PREDICTION" \
sim:/tb_wrapper/ceres_wrapper/i_soc/ex_pc_target_last \
sim:/tb_wrapper/ceres_wrapper/i_soc/ex_pc_sel \


add wave -position insertpoint -radix hexadecimal    -in          -group "WRAPPER" -group "SOC"  -group "FETCH1" -group "BRANCH PREDICTION"     -group in        sim:/tb_wrapper/ceres_wrapper/i_soc/fetch/branch_prediction/*
add wave -position insertpoint -radix hexadecimal    -out         -group "WRAPPER" -group "SOC"  -group "FETCH1" -group "BRANCH PREDICTION"     -group out       sim:/tb_wrapper/ceres_wrapper/i_soc/fetch/branch_prediction/*
add wave -position insertpoint -radix hexadecimal    -internal    -group "WRAPPER" -group "SOC"  -group "FETCH1" -group "BRANCH PREDICTION"     -group internal  sim:/tb_wrapper/ceres_wrapper/i_soc/fetch/branch_prediction/*
add wave -position insertpoint -radix hexadecimal     -in         -group "WRAPPER" -group "SOC"  -group "FETCH1" -group "BRANCH PREDICTION"  -group "RAS"  -group in         sim:/tb_wrapper/ceres_wrapper/i_soc/fetch/branch_prediction/ras/*
add wave -position insertpoint -radix hexadecimal     -out        -group "WRAPPER" -group "SOC"  -group "FETCH1" -group "BRANCH PREDICTION"  -group "RAS"  -group out        sim:/tb_wrapper/ceres_wrapper/i_soc/fetch/branch_prediction/ras/*
add wave -position insertpoint -radix hexadecimal     -internal   -group "WRAPPER" -group "SOC"  -group "FETCH1" -group "BRANCH PREDICTION"  -group "RAS"  -group internal   sim:/tb_wrapper/ceres_wrapper/i_soc/fetch/branch_prediction/ras/*
add wave -position insertpoint -radix hexadecimal        -group "WRAPPER" -group "SOC"  -group "FETCH1" -group "IPMA"                    sim:/tb_wrapper/ceres_wrapper/i_soc/fetch/ipma/*


################## ALIGN BUFFER ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC"  -group "FETCH1" -group "ALIGN BUFFER" -group in       sim:/tb_wrapper/ceres_wrapper/i_soc/fetch/align_buffer/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC"  -group "FETCH1" -group "ALIGN BUFFER" -group out      sim:/tb_wrapper/ceres_wrapper/i_soc/fetch/align_buffer/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC"  -group "FETCH1" -group "ALIGN BUFFER" -group internal sim:/tb_wrapper/ceres_wrapper/i_soc/fetch/align_buffer/*

################## ICACHE TOP ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC"  -group "FETCH1" -group "ICACHE" -group in       sim:/tb_wrapper/ceres_wrapper/i_soc/fetch/icache/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC"  -group "FETCH1" -group "ICACHE" -group out      sim:/tb_wrapper/ceres_wrapper/i_soc/fetch/icache/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC"  -group "FETCH1" -group "ICACHE" -group internal sim:/tb_wrapper/ceres_wrapper/i_soc/fetch/icache/*

################## COMPRESSED DECODER ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC"  -group "FETCH1" -group "COMP DECODER" -group in       sim:/tb_wrapper/ceres_wrapper/i_soc/fetch/compressed_decoder/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC"  -group "FETCH1" -group "COMP DECODER" -group out      sim:/tb_wrapper/ceres_wrapper/i_soc/fetch/compressed_decoder/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC"  -group "FETCH1" -group "COMP DECODER" -group internal sim:/tb_wrapper/ceres_wrapper/i_soc/fetch/compressed_decoder/*

################## CONTROL UNIT ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC"  -group "DECODE2" -group "CONTROL UNIT" -group in       sim:/tb_wrapper/ceres_wrapper/i_soc/i_decode/control_unit/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC"  -group "DECODE2" -group "CONTROL UNIT" -group out      sim:/tb_wrapper/ceres_wrapper/i_soc/i_decode/control_unit/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC"  -group "DECODE2" -group "CONTROL UNIT" -group internal sim:/tb_wrapper/ceres_wrapper/i_soc/i_decode/control_unit/*

################## REG FILE ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC"  -group "DECODE2" -group "REG FILE" -group in       sim:/tb_wrapper/ceres_wrapper/i_soc/i_decode/reg_file/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC"  -group "DECODE2" -group "REG FILE" -group out      sim:/tb_wrapper/ceres_wrapper/i_soc/i_decode/reg_file/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC"  -group "DECODE2" -group "REG FILE" -group internal sim:/tb_wrapper/ceres_wrapper/i_soc/i_decode/reg_file/*

################## EXTEND ##################
add wave -position insertpoint -radix hexadecimal        -group "WRAPPER" -group "SOC"  -group "DECODE2" -group "EXTEND" -group in       sim:/tb_wrapper/ceres_wrapper/i_soc/i_decode/extend/*

################## ALU ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC"  -group "EXECUTION3" -group "ALU" -group in       sim:/tb_wrapper/ceres_wrapper/i_soc/execution/alu/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC"  -group "EXECUTION3" -group "ALU" -group out      sim:/tb_wrapper/ceres_wrapper/i_soc/execution/alu/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC"  -group "EXECUTION3" -group "ALU" -group internal sim:/tb_wrapper/ceres_wrapper/i_soc/execution/alu/*

################## CS_RF ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC"  -group "EXECUTION3" -group "CSR" -group in       sim:/tb_wrapper/ceres_wrapper/i_soc/execution/u_cs_reg_file/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC"  -group "EXECUTION3" -group "CSR" -group out      sim:/tb_wrapper/ceres_wrapper/i_soc/execution/u_cs_reg_file/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC"  -group "EXECUTION3" -group "CSR" -group internal sim:/tb_wrapper/ceres_wrapper/i_soc/execution/u_cs_reg_file/*


################## DCACHE ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC"  -group "MEMORY4" -group "DCACHE" -group in       sim:/tb_wrapper/ceres_wrapper/i_soc/i_memory/dcache/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC"  -group "MEMORY4" -group "DCACHE" -group out      sim:/tb_wrapper/ceres_wrapper/i_soc/i_memory/dcache/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC"  -group "MEMORY4" -group "DCACHE" -group internal sim:/tb_wrapper/ceres_wrapper/i_soc/i_memory/dcache/*
#add wave -position insertpoint -radix hexadecimal           -group "WRAPPER" -group "SOC"  -group "MEMORY4" -group "DPMA"                   sim:/tb_wrapper/ceres_wrapper/i_soc/i_memory/dpma/*

################## UART ##################
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "MEMORY4" -group "UART"   sim:/tb_wrapper/ceres_wrapper/i_soc/i_memory/uart_inst/*
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "MEMORY4" -group "UART"  -group "UART_TX" sim:/tb_wrapper/ceres_wrapper/i_soc/i_memory/uart_inst/uart_tx/*
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "MEMORY4" -group "UART"  -group "UART_TX" sim:/tb_wrapper/ceres_wrapper/i_soc/i_memory/uart_inst/uart_tx/tx_buffer/*
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "MEMORY4" -group "UART"  -group "UART_RX" sim:/tb_wrapper/ceres_wrapper/i_soc/i_memory/uart_inst/uart_rx/*
add wave -position insertpoint -radix hexadecimal  -group "WRAPPER" -group "SOC"  -group "MEMORY4" -group "UART"  -group "UART_RX" sim:/tb_wrapper/ceres_wrapper/i_soc/i_memory/uart_inst/uart_rx/rx_buffer/*

################## ARBITER ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC"  -group "ARBITER" -group in       sim:/tb_wrapper/ceres_wrapper/i_soc/memory_arbiter/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC"  -group "ARBITER" -group out      sim:/tb_wrapper/ceres_wrapper/i_soc/memory_arbiter/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC"  -group "ARBITER" -group internal sim:/tb_wrapper/ceres_wrapper/i_soc/memory_arbiter/*

################## HAZARD ##################
add wave -position insertpoint -radix hexadecimal -in       -group "WRAPPER" -group "SOC"  -group "HAZARD" -group in       sim:/tb_wrapper/ceres_wrapper/i_soc/hazard_unit/*
add wave -position insertpoint -radix hexadecimal -out      -group "WRAPPER" -group "SOC"  -group "HAZARD" -group out      sim:/tb_wrapper/ceres_wrapper/i_soc/hazard_unit/*
add wave -position insertpoint -radix hexadecimal -internal -group "WRAPPER" -group "SOC"  -group "HAZARD" -group internal sim:/tb_wrapper/ceres_wrapper/i_soc/hazard_unit/*


run 10000ns
wave zoom full