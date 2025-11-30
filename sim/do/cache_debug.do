##################################################################################
#                     CERES RISC-V — Cache Debug Waveform                       #
##################################################################################
# Focused on: ICache, DCache, Memory Arbiter, Memory Transactions
##################################################################################

################## Hierarchy Paths ##################
set TB        "sim:/tb_wrapper"
set WRAPPER   "$TB/ceres_wrapper"
set SOC       "$WRAPPER/i_soc"
set FETCH     "$SOC/i_fetch"
set MEMORY    "$SOC/i_memory"
set ARBITER   "$SOC/i_memory_arbiter"

################## Wave Configuration ##################
configure wave -namecolwidth 350
configure wave -valuecolwidth 150
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -timelineunits ns

##################################################################################
#                              ICACHE DEBUG                                      #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ INSTRUCTION CACHE ═══════════}

add wave -noupdate -group "ICACHE" -group "Request" -color Cyan $FETCH/i_icache/cache_req_i.valid
add wave -noupdate -group "ICACHE" -group "Request" -color Cyan $FETCH/i_icache/cache_req_i.ready
add wave -noupdate -group "ICACHE" -group "Request" -radix hexadecimal $FETCH/i_icache/cache_req_i.addr

add wave -noupdate -group "ICACHE" -group "Response" -color Green $FETCH/i_icache/cache_res_o.valid
add wave -noupdate -group "ICACHE" -group "Response" -radix hexadecimal $FETCH/i_icache/cache_res_o.data

add wave -noupdate -group "ICACHE" -group "Hit/Miss" -color Yellow $FETCH/i_icache/cache_hit
add wave -noupdate -group "ICACHE" -group "Hit/Miss" -color Red $FETCH/i_icache/cache_miss
add wave -noupdate -group "ICACHE" -group "Hit/Miss" $FETCH/i_icache/cache_hit_vec
add wave -noupdate -group "ICACHE" -group "Hit/Miss" $FETCH/i_icache/cache_valid_vec

add wave -noupdate -group "ICACHE" -group "State Machine" $FETCH/i_icache/state
add wave -noupdate -group "ICACHE" -group "State Machine" $FETCH/i_icache/flush
add wave -noupdate -group "ICACHE" -group "State Machine" -radix unsigned $FETCH/i_icache/flush_index

add wave -noupdate -group "ICACHE" -group "Tag Array" -radix hexadecimal $FETCH/i_icache/tsram.*
add wave -noupdate -group "ICACHE" -group "Data Array" -radix hexadecimal $FETCH/i_icache/dsram.*
add wave -noupdate -group "ICACHE" -group "PLRU" -radix binary $FETCH/i_icache/nsram.*

add wave -noupdate -group "ICACHE" -group "LowX Interface" $FETCH/i_icache/lowX_req_o.valid
add wave -noupdate -group "ICACHE" -group "LowX Interface" -radix hexadecimal $FETCH/i_icache/lowX_req_o.addr
add wave -noupdate -group "ICACHE" -group "LowX Interface" $FETCH/i_icache/lowX_res_i.valid
add wave -noupdate -group "ICACHE" -group "LowX Interface" -radix hexadecimal $FETCH/i_icache/lowX_res_i.data

add wave -noupdate -group "ICACHE" -group "All Signals" -radix hexadecimal $FETCH/i_icache/*

##################################################################################
#                              DCACHE DEBUG                                      #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ DATA CACHE ═══════════}

add wave -noupdate -group "DCACHE" -group "Request" -color Cyan $MEMORY/i_dcache/cache_req_i.valid
add wave -noupdate -group "DCACHE" -group "Request" -color Cyan $MEMORY/i_dcache/cache_req_i.ready
add wave -noupdate -group "DCACHE" -group "Request" -radix hexadecimal $MEMORY/i_dcache/cache_req_i.addr
add wave -noupdate -group "DCACHE" -group "Request" $MEMORY/i_dcache/cache_req_i.rw
add wave -noupdate -group "DCACHE" -group "Request" -radix hexadecimal $MEMORY/i_dcache/cache_req_i.data

add wave -noupdate -group "DCACHE" -group "Response" -color Green $MEMORY/i_dcache/cache_res_o.valid
add wave -noupdate -group "DCACHE" -group "Response" -radix hexadecimal $MEMORY/i_dcache/cache_res_o.data

add wave -noupdate -group "DCACHE" -group "Hit/Miss" -color Yellow $MEMORY/i_dcache/cache_hit
add wave -noupdate -group "DCACHE" -group "Hit/Miss" -color Red $MEMORY/i_dcache/cache_miss
add wave -noupdate -group "DCACHE" -group "Hit/Miss" $MEMORY/i_dcache/cache_hit_vec
add wave -noupdate -group "DCACHE" -group "Hit/Miss" $MEMORY/i_dcache/cache_valid_vec

add wave -noupdate -group "DCACHE" -group "Writeback" -color Orange $MEMORY/i_dcache/write_back
add wave -noupdate -group "DCACHE" -group "Writeback" -radix hexadecimal $MEMORY/i_dcache/evict_tag
add wave -noupdate -group "DCACHE" -group "Writeback" -radix hexadecimal $MEMORY/i_dcache/evict_data
add wave -noupdate -group "DCACHE" -group "Writeback" $MEMORY/i_dcache/fencei_stall_o

add wave -noupdate -group "DCACHE" -group "State Machine" $MEMORY/i_dcache/state
add wave -noupdate -group "DCACHE" -group "State Machine" $MEMORY/i_dcache/fi_state_q
add wave -noupdate -group "DCACHE" -group "State Machine" $MEMORY/i_dcache/flush
add wave -noupdate -group "DCACHE" -group "State Machine" -radix unsigned $MEMORY/i_dcache/flush_index

add wave -noupdate -group "DCACHE" -group "Tag Array" -radix hexadecimal $MEMORY/i_dcache/tsram.*
add wave -noupdate -group "DCACHE" -group "Data Array" -radix hexadecimal $MEMORY/i_dcache/dsram.*
add wave -noupdate -group "DCACHE" -group "Dirty Array" -radix hexadecimal $MEMORY/i_dcache/drsram.*
add wave -noupdate -group "DCACHE" -group "PLRU" -radix binary $MEMORY/i_dcache/nsram.*

add wave -noupdate -group "DCACHE" -group "LowX Interface" $MEMORY/i_dcache/lowX_req_o.valid
add wave -noupdate -group "DCACHE" -group "LowX Interface" -radix hexadecimal $MEMORY/i_dcache/lowX_req_o.addr
add wave -noupdate -group "DCACHE" -group "LowX Interface" $MEMORY/i_dcache/lowX_req_o.rw
add wave -noupdate -group "DCACHE" -group "LowX Interface" -radix hexadecimal $MEMORY/i_dcache/lowX_req_o.data
add wave -noupdate -group "DCACHE" -group "LowX Interface" $MEMORY/i_dcache/lowX_res_i.valid
add wave -noupdate -group "DCACHE" -group "LowX Interface" -radix hexadecimal $MEMORY/i_dcache/lowX_res_i.data

add wave -noupdate -group "DCACHE" -group "All Signals" -radix hexadecimal $MEMORY/i_dcache/*

##################################################################################
#                              MEMORY ARBITER                                    #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ MEMORY ARBITER ═══════════}

add wave -noupdate -group "ARBITER" -group "Round Robin" -color Magenta $ARBITER/round
add wave -noupdate -group "ARBITER" -group "Round Robin" $ARBITER/grant_icache
add wave -noupdate -group "ARBITER" -group "Round Robin" $ARBITER/grant_dcache

add wave -noupdate -group "ARBITER" -group "ICache Port" $ARBITER/icache_req_i.valid
add wave -noupdate -group "ARBITER" -group "ICache Port" -radix hexadecimal $ARBITER/icache_req_i.addr
add wave -noupdate -group "ARBITER" -group "ICache Port" $ARBITER/icache_res_o.valid
add wave -noupdate -group "ARBITER" -group "ICache Port" $ARBITER/icache_res_o.ready
add wave -noupdate -group "ARBITER" -group "ICache Port" -radix hexadecimal $ARBITER/icache_res_o.data

add wave -noupdate -group "ARBITER" -group "DCache Port" $ARBITER/dcache_req_i.valid
add wave -noupdate -group "ARBITER" -group "DCache Port" -radix hexadecimal $ARBITER/dcache_req_i.addr
add wave -noupdate -group "ARBITER" -group "DCache Port" $ARBITER/dcache_req_i.rw
add wave -noupdate -group "ARBITER" -group "DCache Port" -radix hexadecimal $ARBITER/dcache_req_i.data
add wave -noupdate -group "ARBITER" -group "DCache Port" $ARBITER/dcache_res_o.valid
add wave -noupdate -group "ARBITER" -group "DCache Port" $ARBITER/dcache_res_o.ready
add wave -noupdate -group "ARBITER" -group "DCache Port" -radix hexadecimal $ARBITER/dcache_res_o.data

add wave -noupdate -group "ARBITER" -group "IO Memory" $ARBITER/iomem_req_o.valid
add wave -noupdate -group "ARBITER" -group "IO Memory" -radix hexadecimal $ARBITER/iomem_req_o.addr
add wave -noupdate -group "ARBITER" -group "IO Memory" -radix hexadecimal $ARBITER/iomem_req_o.rw
add wave -noupdate -group "ARBITER" -group "IO Memory" -radix hexadecimal $ARBITER/iomem_req_o.data
add wave -noupdate -group "ARBITER" -group "IO Memory" $ARBITER/iomem_res_i.valid
add wave -noupdate -group "ARBITER" -group "IO Memory" $ARBITER/iomem_res_i.ready
add wave -noupdate -group "ARBITER" -group "IO Memory" -radix hexadecimal $ARBITER/iomem_res_i.data

add wave -noupdate -group "ARBITER" -group "All Signals" -radix hexadecimal $ARBITER/*

##################################################################################
#                              MAIN RAM                                          #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ MAIN RAM ═══════════}

add wave -noupdate -group "RAM" -group "Interface" -radix hexadecimal $WRAPPER/ram_addr
add wave -noupdate -group "RAM" -group "Interface" -radix hexadecimal $WRAPPER/ram_wstrb
add wave -noupdate -group "RAM" -group "Interface" $WRAPPER/ram_rd_en
add wave -noupdate -group "RAM" -group "Interface" -radix hexadecimal $WRAPPER/ram_rdata

add wave -noupdate -group "RAM" -group "Latency" -radix binary $WRAPPER/ram_delay_q
add wave -noupdate -group "RAM" -group "Latency" $WRAPPER/ram_pending_q

add wave -noupdate -group "RAM" -group "Wrapper RAM" -radix hexadecimal $WRAPPER/i_main_ram/*

##################################################################################
#                              STALL ANALYSIS                                    #
##################################################################################
add wave -noupdate -divider -height 25 {═══════════ STALL ANALYSIS ═══════════}

add wave -noupdate -group "STALLS" -color Red $SOC/stall_cause
add wave -noupdate -group "STALLS" -color Orange $SOC/fe_imiss_stall
add wave -noupdate -group "STALLS" -color Orange $SOC/me_dmiss_stall
add wave -noupdate -group "STALLS" -color Yellow $SOC/me_fencei_stall
add wave -noupdate -group "STALLS" -color Magenta $SOC/ex_alu_stall

##################################################################################
#                              RUN SIMULATION                                    #
##################################################################################
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ns} 0}
configure wave -timelineunits ns
run 10000ns
wave zoom full

puts "═══════════════════════════════════════════════════════════════════"
puts "  CERES Cache Debug Waveform Loaded!"
puts "═══════════════════════════════════════════════════════════════════"
