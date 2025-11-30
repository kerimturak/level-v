##################################################################################
#                      CERES RISC-V — Memory Access Debug                       #
##################################################################################
# Focused on: Load/Store operations, DPMA, Address translation
##################################################################################

################## Hierarchy Paths ##################
set TB        "sim:/tb_wrapper"
set WRAPPER   "$TB/ceres_wrapper"
set SOC       "$WRAPPER/i_soc"
set MEMORY    "$SOC/i_memory"
set DCACHE    "$MEMORY/i_dcache"
set DPMA      "$MEMORY/i_dpma"
set ARBITER   "$SOC/i_memory_arbiter"

################## Wave Configuration ##################
configure wave -namecolwidth 350
configure wave -valuecolwidth 150
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -timelineunits ns

##################################################################################
#                              MEMORY STAGE                                      #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ MEMORY STAGE ═══════════}

add wave -noupdate -group "MEM STAGE" -color Gold $TB/clk_i
add wave -noupdate -group "MEM STAGE" -radix hex $MEMORY/pc_i
add wave -noupdate -group "MEM STAGE" $MEMORY/mem_rw_i
add wave -noupdate -group "MEM STAGE" $MEMORY/dmiss_stall_o

add wave -noupdate -group "MEM STAGE" -group "Address" -radix hex $MEMORY/alu_result_i
add wave -noupdate -group "MEM STAGE" -group "Address" -radix hex $MEMORY/dm_addr
add wave -noupdate -group "MEM STAGE" -group "Address" $MEMORY/dm_align

add wave -noupdate -group "MEM STAGE" -group "Write Data" -radix hex $MEMORY/r2_data_i
add wave -noupdate -group "MEM STAGE" -group "Write Data" -radix hex $MEMORY/dm_wdata
add wave -noupdate -group "MEM STAGE" -group "Write Data" $MEMORY/dm_wmask

add wave -noupdate -group "MEM STAGE" -group "Read Data" -radix hex $MEMORY/dm_rdata
add wave -noupdate -group "MEM STAGE" -group "Read Data" -radix hex $MEMORY/mem_data_o
add wave -noupdate -group "MEM STAGE" -group "Read Data" $MEMORY/ldst_type_i

##################################################################################
#                              DPMA (Physical Memory Attributes)                 #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ DPMA ═══════════}

add wave -noupdate -group "DPMA" -radix hex $DPMA/addr_i
add wave -noupdate -group "DPMA" -radix hex $DPMA/wdata_i
add wave -noupdate -group "DPMA" -radix hex $DPMA/rdata_o
add wave -noupdate -group "DPMA" $DPMA/mem_rw_i
add wave -noupdate -group "DPMA" $DPMA/wmask_i
add wave -noupdate -group "DPMA" $DPMA/rvalid_o
add wave -noupdate -group "DPMA" $DPMA/wready_o

add wave -noupdate -group "DPMA" -group "Peripheral Select" $DPMA/periph_sel
add wave -noupdate -group "DPMA" -group "Peripheral Select" $DPMA/ram_sel
add wave -noupdate -group "DPMA" -group "Peripheral Select" $DPMA/uart_sel

add wave -noupdate -group "DPMA" -group "All" -radix hex $DPMA/*

##################################################################################
#                              DCACHE                                            #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ DCACHE ═══════════}

add wave -noupdate -group "DCACHE" -group "CPU Interface" $DCACHE/enable_i
add wave -noupdate -group "DCACHE" -group "CPU Interface" -radix hex $DCACHE/addr_i
add wave -noupdate -group "DCACHE" -group "CPU Interface" -radix hex $DCACHE/wdata_i
add wave -noupdate -group "DCACHE" -group "CPU Interface" -radix hex $DCACHE/rdata_o
add wave -noupdate -group "DCACHE" -group "CPU Interface" $DCACHE/rw_i
add wave -noupdate -group "DCACHE" -group "CPU Interface" $DCACHE/wmask_i
add wave -noupdate -group "DCACHE" -group "CPU Interface" $DCACHE/stall_o

add wave -noupdate -group "DCACHE" -group "Cache State" $DCACHE/state
add wave -noupdate -group "DCACHE" -group "Cache State" $DCACHE/hit
add wave -noupdate -group "DCACHE" -group "Cache State" $DCACHE/miss
add wave -noupdate -group "DCACHE" -group "Cache State" $DCACHE/dirty

add wave -noupdate -group "DCACHE" -group "Tag/Index" -radix hex $DCACHE/tag
add wave -noupdate -group "DCACHE" -group "Tag/Index" -radix hex $DCACHE/index
add wave -noupdate -group "DCACHE" -group "Tag/Index" -radix hex $DCACHE/offset

add wave -noupdate -group "DCACHE" -group "Memory Interface" $DCACHE/mem_req
add wave -noupdate -group "DCACHE" -group "Memory Interface" $DCACHE/mem_ack
add wave -noupdate -group "DCACHE" -group "Memory Interface" -radix hex $DCACHE/mem_addr
add wave -noupdate -group "DCACHE" -group "Memory Interface" -radix hex $DCACHE/mem_wdata
add wave -noupdate -group "DCACHE" -group "Memory Interface" -radix hex $DCACHE/mem_rdata

add wave -noupdate -group "DCACHE" -group "All" -radix hex $DCACHE/*

##################################################################################
#                              MEMORY ARBITER                                    #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ MEMORY ARBITER ═══════════}

add wave -noupdate -group "ARBITER" -color Gold $TB/clk_i
add wave -noupdate -group "ARBITER" $ARBITER/state

add wave -noupdate -group "ARBITER" -group "I$ Request" -color Cyan $ARBITER/icache_req_i
add wave -noupdate -group "ARBITER" -group "I$ Request" -color Cyan $ARBITER/icache_ack_o
add wave -noupdate -group "ARBITER" -group "I$ Request" -radix hex $ARBITER/icache_addr_i
add wave -noupdate -group "ARBITER" -group "I$ Request" -radix hex $ARBITER/icache_data_o

add wave -noupdate -group "ARBITER" -group "D$ Request" -color Yellow $ARBITER/dcache_req_i
add wave -noupdate -group "ARBITER" -group "D$ Request" -color Yellow $ARBITER/dcache_ack_o
add wave -noupdate -group "ARBITER" -group "D$ Request" $ARBITER/dcache_rw_i
add wave -noupdate -group "ARBITER" -group "D$ Request" -radix hex $ARBITER/dcache_addr_i
add wave -noupdate -group "ARBITER" -group "D$ Request" -radix hex $ARBITER/dcache_wdata_i
add wave -noupdate -group "ARBITER" -group "D$ Request" -radix hex $ARBITER/dcache_data_o

add wave -noupdate -group "ARBITER" -group "Memory Bus" -color Magenta $ARBITER/mem_req_o
add wave -noupdate -group "ARBITER" -group "Memory Bus" -color Magenta $ARBITER/mem_ack_i
add wave -noupdate -group "ARBITER" -group "Memory Bus" $ARBITER/mem_rw_o
add wave -noupdate -group "ARBITER" -group "Memory Bus" -radix hex $ARBITER/mem_addr_o
add wave -noupdate -group "ARBITER" -group "Memory Bus" -radix hex $ARBITER/mem_wdata_o
add wave -noupdate -group "ARBITER" -group "Memory Bus" -radix hex $ARBITER/mem_data_i

add wave -noupdate -group "ARBITER" -group "All" -radix hex $ARBITER/*

##################################################################################
#                              MAIN RAM                                          #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ MAIN RAM ═══════════}

add wave -noupdate -group "RAM" -radix hex $WRAPPER/i_main_ram/*

##################################################################################
#                              UART                                              #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ UART ═══════════}

add wave -noupdate -group "UART" $MEMORY/i_uart/cs_i
add wave -noupdate -group "UART" $MEMORY/i_uart/we_i
add wave -noupdate -group "UART" -radix hex $MEMORY/i_uart/addr_i
add wave -noupdate -group "UART" -radix hex $MEMORY/i_uart/wdata_i
add wave -noupdate -group "UART" -radix hex $MEMORY/i_uart/rdata_o

add wave -noupdate -group "UART" -group "TX" $MEMORY/i_uart/tx_o
add wave -noupdate -group "UART" -group "TX" $MEMORY/i_uart/i_uart_tx/busy

add wave -noupdate -group "UART" -group "RX" $MEMORY/i_uart/rx_i
add wave -noupdate -group "UART" -group "RX" $MEMORY/i_uart/i_uart_rx/valid

add wave -noupdate -group "UART" -group "All" -radix hex $MEMORY/i_uart/*

##################################################################################
#                              LOAD/STORE TRACKING                               #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ LOAD/STORE TRACKING ═══════════}

add wave -noupdate -group "LD/ST" -radix hex $SOC/pipe3.pc
add wave -noupdate -group "LD/ST" $SOC/pipe3.instr_type
add wave -noupdate -group "LD/ST" $SOC/pipe3.ldst_type
add wave -noupdate -group "LD/ST" $SOC/pipe3.mem_rw_en
add wave -noupdate -group "LD/ST" -radix hex $SOC/pipe3.alu_result
add wave -noupdate -group "LD/ST" -radix hex $SOC/pipe3.r2_data

##################################################################################
#                              RUN SIMULATION                                    #
##################################################################################
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ns} 0}
configure wave -timelineunits ns
run 10000ns
wave zoom full

puts "═══════════════════════════════════════════════════════════════════"
puts "  CERES Memory Access Debug Waveform Loaded!"
puts "═══════════════════════════════════════════════════════════════════"
