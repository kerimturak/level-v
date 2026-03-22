##################################################################################
#                     Level RISC-V — Advanced Debug Waveform                   #
#                           Questa Simulation Script                            #
##################################################################################
# Features:
#   - Hierarchical grouping by pipeline stage
#   - Color-coded signal categories
#   - Automatic radix selection (hex/decimal/binary)
#   - Collapsible groups for easy navigation
#   - Critical path signals highlighted
#   - Exception/Interrupt debugging section
#   - Performance counter monitoring
#   - Memory transaction tracking
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

################## Wave Configuration ##################
configure wave -namecolwidth 300
configure wave -valuecolwidth 120
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns

################## Hierarchy Paths ##################
set TB        "sim:/tb_wrapper"
set WRAPPER   "$TB/level_wrapper"
set SOC       "$WRAPPER/i_soc"
set FETCH     "$SOC/i_fetch"
set DECODE    "$SOC/i_decode"
set EXECUTE   "$SOC/i_execution"
set MEMORY    "$SOC/i_memory"
set WRITEBACK "$SOC/i_writeback"
set HAZARD    "$SOC/i_hazard_unit"
set ARBITER   "$SOC/i_memory_arbiter"

##################################################################################
#                              🎯 QUICK DEBUG VIEW                               #
##################################################################################
add wave -noupdate -divider -height 20 {═══════════ QUICK DEBUG ═══════════}

# Clock & Reset
add wave -noupdate -group "⏱️ CLK/RST" -color Gold      $TB/clk_i
add wave -noupdate -group "⏱️ CLK/RST" -color Orange    $TB/rst_ni

# Pipeline Progress (Critical Signals)
add wave -noupdate -group "🔄 PIPELINE" -color Cyan     -radix hexadecimal $SOC/fe_pc
add wave -noupdate -group "🔄 PIPELINE" -color Cyan     -radix hexadecimal $SOC/fe_inst
add wave -noupdate -group "🔄 PIPELINE" -color Green    -radix hexadecimal $SOC/pipe1.pc
add wave -noupdate -group "🔄 PIPELINE" -color Green    -radix hexadecimal $SOC/pipe1.inst
add wave -noupdate -group "🔄 PIPELINE" -color Yellow   -radix hexadecimal $SOC/pipe2.pc
add wave -noupdate -group "🔄 PIPELINE" -color Magenta  -radix hexadecimal $SOC/pipe3.pc
add wave -noupdate -group "🔄 PIPELINE" -color Red      -radix hexadecimal $SOC/pipe4.pc

# Stall & Flush (Debug Critical)
add wave -noupdate -group "⚠️ STALL/FLUSH" -color Red       $SOC/stall_cause
add wave -noupdate -group "⚠️ STALL/FLUSH" -color Orange    $SOC/fe_imiss_stall
add wave -noupdate -group "⚠️ STALL/FLUSH" -color Orange    $SOC/me_dmiss_stall
add wave -noupdate -group "⚠️ STALL/FLUSH" -color Orange    $SOC/ex_alu_stall
add wave -noupdate -group "⚠️ STALL/FLUSH" -color Yellow    $SOC/me_fencei_stall
add wave -noupdate -group "⚠️ STALL/FLUSH" -color Magenta   $SOC/de_flush
add wave -noupdate -group "⚠️ STALL/FLUSH" -color Magenta   $SOC/ex_flush
add wave -noupdate -group "⚠️ STALL/FLUSH" -color Magenta   $SOC/fencei_flush
add wave -noupdate -group "⚠️ STALL/FLUSH" -color Red       $SOC/priority_flush

# Register File Quick View
add wave -noupdate -group "📝 REGFILE" -radix hexadecimal $DECODE/i_reg_file/registers

##################################################################################
#                            🚨 EXCEPTION DEBUGGING                              #
##################################################################################
add wave -noupdate -divider -height 20 {═══════════ EXCEPTIONS ═══════════}

add wave -noupdate -group "🚨 EXCEPTIONS" -color Red    $SOC/trap_active
add wave -noupdate -group "🚨 EXCEPTIONS" -color Red    $SOC/fe_trap_active
add wave -noupdate -group "🚨 EXCEPTIONS" -color Red    $SOC/de_trap_active
add wave -noupdate -group "🚨 EXCEPTIONS" -color Orange $SOC/fe_exc_type
add wave -noupdate -group "🚨 EXCEPTIONS" -color Orange $SOC/de_exc_type
add wave -noupdate -group "🚨 EXCEPTIONS" -color Orange $SOC/ex_exc_type
add wave -noupdate -group "🚨 EXCEPTIONS" -color Orange $SOC/ex_alu_exc_type
add wave -noupdate -group "🚨 EXCEPTIONS" -color Yellow -radix hexadecimal $SOC/trap_tval
add wave -noupdate -group "🚨 EXCEPTIONS" -color Yellow -radix hexadecimal $SOC/ex_trap_cause
add wave -noupdate -group "🚨 EXCEPTIONS" -color Yellow -radix hexadecimal $SOC/ex_trap_mepc
add wave -noupdate -group "🚨 EXCEPTIONS" -color Cyan   -radix hexadecimal $SOC/ex_mtvec
add wave -noupdate -group "🚨 EXCEPTIONS" -color Green  $SOC/excp_mask

##################################################################################
#                          🎯 BRANCH PREDICTION DEBUG                            #
##################################################################################
add wave -noupdate -divider -height 20 {═══════════ BRANCH PRED ═══════════}

add wave -noupdate -group "🎯 BRANCH PRED" -group "Outcome" -color Green  $SOC/ex_spec_hit
add wave -noupdate -group "🎯 BRANCH PRED" -group "Outcome" -color Red    $SOC/ex_pc_sel
add wave -noupdate -group "🎯 BRANCH PRED" -group "Outcome" -radix hexadecimal $SOC/ex_pc_target
add wave -noupdate -group "🎯 BRANCH PRED" -group "Outcome" -radix hexadecimal $SOC/ex_pc_target_last

add wave -noupdate -group "🎯 BRANCH PRED" -group "Speculation" $SOC/fe_spec.taken
add wave -noupdate -group "🎯 BRANCH PRED" -group "Speculation" $SOC/fe_spec.spectype
add wave -noupdate -group "🎯 BRANCH PRED" -group "Speculation" -radix hexadecimal $SOC/fe_spec.pc

add wave -noupdate -group "🎯 BRANCH PRED" -group "GShare" -radix hexadecimal $FETCH/i_gshare_bp/*
add wave -noupdate -group "🎯 BRANCH PRED" -group "RAS"    -radix hexadecimal $FETCH/i_gshare_bp/i_ras/*

##################################################################################
#                           📥 STAGE 1: FETCH                                    #
##################################################################################
add wave -noupdate -divider -height 20 {═══════════ FETCH ═══════════}

add wave -noupdate -group "📥 FETCH" -group "PC Logic" -color Cyan -radix hexadecimal $FETCH/pc_o
add wave -noupdate -group "📥 FETCH" -group "PC Logic" -radix hexadecimal $FETCH/pc_incr_o
add wave -noupdate -group "📥 FETCH" -group "PC Logic" -radix hexadecimal $FETCH/pc_next
add wave -noupdate -group "📥 FETCH" -group "PC Logic" $FETCH/pc_en

add wave -noupdate -group "📥 FETCH" -group "Instruction" -radix hexadecimal $FETCH/inst_o
add wave -noupdate -group "📥 FETCH" -group "Instruction" $FETCH/is_comp
add wave -noupdate -group "📥 FETCH" -group "Instruction" $FETCH/illegal_instr
add wave -noupdate -group "📥 FETCH" -group "Instruction" $FETCH/instr_type_o

add wave -noupdate -group "📥 FETCH" -group "Control" $FETCH/flush_i
add wave -noupdate -group "📥 FETCH" -group "Control" $FETCH/stall_i
add wave -noupdate -group "📥 FETCH" -group "Control" $FETCH/imiss_stall_o
add wave -noupdate -group "📥 FETCH" -group "Control" $FETCH/exc_type_o

add wave -noupdate -group "📥 FETCH" -group "ICache" -radix hexadecimal $FETCH/i_icache/*
add wave -noupdate -group "📥 FETCH" -group "Align Buffer" -radix hexadecimal $FETCH/i_align_buffer/*
add wave -noupdate -group "📥 FETCH" -group "Comp Decoder" -radix hexadecimal $FETCH/i_compressed_decoder/*
add wave -noupdate -group "📥 FETCH" -group "PMA" -radix hexadecimal $FETCH/i_pma/*

##################################################################################
#                           📋 STAGE 2: DECODE                                   #
##################################################################################
add wave -noupdate -divider -height 20 {═══════════ DECODE ═══════════}

add wave -noupdate -group "📋 DECODE" -group "Input" -radix hexadecimal $SOC/pipe1.pc
add wave -noupdate -group "📋 DECODE" -group "Input" -radix hexadecimal $SOC/pipe1.inst
add wave -noupdate -group "📋 DECODE" -group "Input" $SOC/pipe1.instr_type

add wave -noupdate -group "📋 DECODE" -group "Control" -radix hexadecimal $DECODE/ctrl_o
add wave -noupdate -group "📋 DECODE" -group "Control" $DECODE/exc_type_o

add wave -noupdate -group "📋 DECODE" -group "Registers" -radix hexadecimal $DECODE/r1_data_o
add wave -noupdate -group "📋 DECODE" -group "Registers" -radix hexadecimal $DECODE/r2_data_o
add wave -noupdate -group "📋 DECODE" -group "Registers" -radix hexadecimal $DECODE/imm_o
add wave -noupdate -group "📋 DECODE" -group "Registers" $DECODE/fwd_a_i
add wave -noupdate -group "📋 DECODE" -group "Registers" $DECODE/fwd_b_i

add wave -noupdate -group "📋 DECODE" -group "Control Unit" -radix hexadecimal $DECODE/i_control_unit/*
add wave -noupdate -group "📋 DECODE" -group "Reg File" -radix hexadecimal $DECODE/i_reg_file/*
add wave -noupdate -group "📋 DECODE" -group "Extend" -radix hexadecimal $DECODE/i_extend/*

##################################################################################
#                           ⚙️ STAGE 3: EXECUTE                                  #
##################################################################################
add wave -noupdate -divider -height 20 {═══════════ EXECUTE ═══════════}

add wave -noupdate -group "⚙️ EXECUTE" -group "Input" -radix hexadecimal $SOC/pipe2.pc
add wave -noupdate -group "⚙️ EXECUTE" -group "Input" $SOC/pipe2.instr_type
add wave -noupdate -group "⚙️ EXECUTE" -group "Input" -radix hexadecimal $SOC/pipe2.r1_data
add wave -noupdate -group "⚙️ EXECUTE" -group "Input" -radix hexadecimal $SOC/pipe2.r2_data
add wave -noupdate -group "⚙️ EXECUTE" -group "Input" -radix hexadecimal $SOC/pipe2.imm

add wave -noupdate -group "⚙️ EXECUTE" -group "ALU" -radix hexadecimal $EXECUTE/i_alu/alu_a_i
add wave -noupdate -group "⚙️ EXECUTE" -group "ALU" -radix hexadecimal $EXECUTE/i_alu/alu_b_i
add wave -noupdate -group "⚙️ EXECUTE" -group "ALU" $EXECUTE/i_alu/op_sel_i
add wave -noupdate -group "⚙️ EXECUTE" -group "ALU" -radix hexadecimal $EXECUTE/i_alu/alu_o
add wave -noupdate -group "⚙️ EXECUTE" -group "ALU" $EXECUTE/i_alu/zero_o
add wave -noupdate -group "⚙️ EXECUTE" -group "ALU" $EXECUTE/i_alu/slt_o
add wave -noupdate -group "⚙️ EXECUTE" -group "ALU" $EXECUTE/i_alu/sltu_o
add wave -noupdate -group "⚙️ EXECUTE" -group "ALU" $EXECUTE/i_alu/alu_stall_o

add wave -noupdate -group "⚙️ EXECUTE" -group "Mul/Div" -radix hexadecimal $EXECUTE/i_alu/*mul*
add wave -noupdate -group "⚙️ EXECUTE" -group "Mul/Div" -radix hexadecimal $EXECUTE/i_alu/*div*

add wave -noupdate -group "⚙️ EXECUTE" -group "Branch" $EXECUTE/pc_sel_i
add wave -noupdate -group "⚙️ EXECUTE" -group "Branch" $EXECUTE/pc_sel_o
add wave -noupdate -group "⚙️ EXECUTE" -group "Branch" -radix hexadecimal $EXECUTE/pc_target_o

add wave -noupdate -group "⚙️ EXECUTE" -group "Forwarding" $SOC/ex_fwd_a
add wave -noupdate -group "⚙️ EXECUTE" -group "Forwarding" $SOC/ex_fwd_b

add wave -noupdate -group "⚙️ EXECUTE" -group "CSR" -radix hexadecimal $EXECUTE/i_cs_reg_file/*

##################################################################################
#                           💾 STAGE 4: MEMORY                                   #
##################################################################################
add wave -noupdate -divider -height 20 {═══════════ MEMORY ═══════════}

add wave -noupdate -group "💾 MEMORY" -group "Input" -radix hexadecimal $SOC/pipe3.pc
add wave -noupdate -group "💾 MEMORY" -group "Input" -radix hexadecimal $SOC/pipe3.alu_result
add wave -noupdate -group "💾 MEMORY" -group "Input" -radix hexadecimal $SOC/pipe3.write_data
add wave -noupdate -group "💾 MEMORY" -group "Input" $SOC/pipe3.wr_en
add wave -noupdate -group "💾 MEMORY" -group "Input" $SOC/pipe3.rw_size

add wave -noupdate -group "💾 MEMORY" -group "Data Request" $SOC/ex_data_req.valid
add wave -noupdate -group "💾 MEMORY" -group "Data Request" -radix hexadecimal $SOC/ex_data_req.addr
add wave -noupdate -group "💾 MEMORY" -group "Data Request" $SOC/ex_data_req.rw
add wave -noupdate -group "💾 MEMORY" -group "Data Request" -radix hexadecimal $SOC/ex_data_req.data

add wave -noupdate -group "💾 MEMORY" -group "DCache" -radix hexadecimal $MEMORY/i_dcache/*
add wave -noupdate -group "💾 MEMORY" -group "PMA" -radix hexadecimal $MEMORY/i_dpma/*

add wave -noupdate -group "💾 MEMORY" -group "Output" -radix hexadecimal $MEMORY/me_data_o
add wave -noupdate -group "💾 MEMORY" -group "Output" $MEMORY/dmiss_stall_o
add wave -noupdate -group "💾 MEMORY" -group "Output" $MEMORY/fencei_stall_o

add wave -noupdate -group "💾 MEMORY" -group "UART" -radix hexadecimal $MEMORY/i_uart/*
add wave -noupdate -group "💾 MEMORY" -group "UART TX" -radix hexadecimal $MEMORY/i_uart/i_uart_tx/*
add wave -noupdate -group "💾 MEMORY" -group "UART RX" -radix hexadecimal $MEMORY/i_uart/i_uart_rx/*

##################################################################################
#                           ✅ STAGE 5: WRITEBACK                                #
##################################################################################
add wave -noupdate -divider -height 20 {═══════════ WRITEBACK ═══════════}

add wave -noupdate -group "✅ WRITEBACK" -group "Input" -radix hexadecimal $SOC/pipe4.pc
add wave -noupdate -group "✅ WRITEBACK" -group "Input" -radix hexadecimal $SOC/pipe4.alu_result
add wave -noupdate -group "✅ WRITEBACK" -group "Input" -radix hexadecimal $SOC/pipe4.read_data
add wave -noupdate -group "✅ WRITEBACK" -group "Input" $SOC/pipe4.result_src
add wave -noupdate -group "✅ WRITEBACK" -group "Input" $SOC/pipe4.rf_rw_en
add wave -noupdate -group "✅ WRITEBACK" -group "Input" -radix unsigned $SOC/pipe4.rd_addr

add wave -noupdate -group "✅ WRITEBACK" -group "Output" $WRITEBACK/rf_rw_en_o
add wave -noupdate -group "✅ WRITEBACK" -group "Output" -radix hexadecimal $WRITEBACK/wb_data_o

##################################################################################
#                           🔀 HAZARD UNIT                                       #
##################################################################################
add wave -noupdate -divider -height 20 {═══════════ HAZARD ═══════════}

add wave -noupdate -group "🔀 HAZARD" -group "Stalls" $HAZARD/stall_fe_o
add wave -noupdate -group "🔀 HAZARD" -group "Stalls" $HAZARD/stall_de_o

add wave -noupdate -group "🔀 HAZARD" -group "Flushes" $HAZARD/flush_de_o
add wave -noupdate -group "🔀 HAZARD" -group "Flushes" $HAZARD/flush_ex_o

add wave -noupdate -group "🔀 HAZARD" -group "Forwarding EX" $HAZARD/fwd_a_ex_o
add wave -noupdate -group "🔀 HAZARD" -group "Forwarding EX" $HAZARD/fwd_b_ex_o
add wave -noupdate -group "🔀 HAZARD" -group "Forwarding DE" $HAZARD/fwd_a_de_o
add wave -noupdate -group "🔀 HAZARD" -group "Forwarding DE" $HAZARD/fwd_b_de_o

add wave -noupdate -group "🔀 HAZARD" -group "Register Addresses" -radix unsigned $HAZARD/r1_addr_de_i
add wave -noupdate -group "🔀 HAZARD" -group "Register Addresses" -radix unsigned $HAZARD/r2_addr_de_i
add wave -noupdate -group "🔀 HAZARD" -group "Register Addresses" -radix unsigned $HAZARD/rd_addr_ex_i
add wave -noupdate -group "🔀 HAZARD" -group "Register Addresses" -radix unsigned $HAZARD/rd_addr_me_i
add wave -noupdate -group "🔀 HAZARD" -group "Register Addresses" -radix unsigned $HAZARD/rd_addr_wb_i

##################################################################################
#                           🔁 MEMORY ARBITER                                    #
##################################################################################
add wave -noupdate -divider -height 20 {═══════════ ARBITER ═══════════}

add wave -noupdate -group "🔁 ARBITER" -group "ICache Request" $ARBITER/icache_req_i.valid
add wave -noupdate -group "🔁 ARBITER" -group "ICache Request" -radix hexadecimal $ARBITER/icache_req_i.addr
add wave -noupdate -group "🔁 ARBITER" -group "ICache Response" $ARBITER/icache_res_o.valid
add wave -noupdate -group "🔁 ARBITER" -group "ICache Response" -radix hexadecimal $ARBITER/icache_res_o.data

add wave -noupdate -group "🔁 ARBITER" -group "DCache Request" $ARBITER/dcache_req_i.valid
add wave -noupdate -group "🔁 ARBITER" -group "DCache Request" -radix hexadecimal $ARBITER/dcache_req_i.addr
add wave -noupdate -group "🔁 ARBITER" -group "DCache Response" $ARBITER/dcache_res_o.valid
add wave -noupdate -group "🔁 ARBITER" -group "DCache Response" -radix hexadecimal $ARBITER/dcache_res_o.data

add wave -noupdate -group "🔁 ARBITER" -group "IO Memory" $ARBITER/iomem_req_o.valid
add wave -noupdate -group "🔁 ARBITER" -group "IO Memory" -radix hexadecimal $ARBITER/iomem_req_o.addr
add wave -noupdate -group "🔁 ARBITER" -group "IO Memory" $ARBITER/iomem_res_i.valid
add wave -noupdate -group "🔁 ARBITER" -group "IO Memory" -radix hexadecimal $ARBITER/iomem_res_i.data

add wave -noupdate -group "🔁 ARBITER" -group "Internal" -radix hexadecimal $ARBITER/*

##################################################################################
#                           🏠 WRAPPER / TOP LEVEL                               #
##################################################################################
add wave -noupdate -divider -height 20 {═══════════ WRAPPER ═══════════}

add wave -noupdate -group "🏠 WRAPPER" -group "External IO" $TB/clk_i
add wave -noupdate -group "🏠 WRAPPER" -group "External IO" $TB/rst_ni
add wave -noupdate -group "🏠 WRAPPER" -group "External IO" $WRAPPER/uart_tx_o
add wave -noupdate -group "🏠 WRAPPER" -group "External IO" $WRAPPER/uart_rx_i

add wave -noupdate -group "🏠 WRAPPER" -group "Memory Interface" $WRAPPER/cpu_mem_req.valid
add wave -noupdate -group "🏠 WRAPPER" -group "Memory Interface" -radix hexadecimal $WRAPPER/cpu_mem_req.addr
add wave -noupdate -group "🏠 WRAPPER" -group "Memory Interface" -radix hexadecimal $WRAPPER/cpu_mem_req.data
add wave -noupdate -group "🏠 WRAPPER" -group "Memory Interface" $WRAPPER/cpu_mem_res.valid
add wave -noupdate -group "🏠 WRAPPER" -group "Memory Interface" -radix hexadecimal $WRAPPER/cpu_mem_res.data

add wave -noupdate -group "🏠 WRAPPER" -group "RAM" -radix hexadecimal $WRAPPER/i_main_ram/*

##################################################################################
#                           📊 ALL INTERNAL SIGNALS                              #
##################################################################################
add wave -noupdate -divider -height 20 {═══════════ DETAILED VIEW ═══════════}

# Detailed groups for deep debugging (collapsed by default)
add wave -noupdate -group "📊 SOC Internal" -radix hexadecimal $SOC/*
add wave -noupdate -group "📊 FETCH Internal" -radix hexadecimal $FETCH/*
add wave -noupdate -group "📊 DECODE Internal" -radix hexadecimal $DECODE/*
add wave -noupdate -group "📊 EXECUTE Internal" -radix hexadecimal $EXECUTE/*
add wave -noupdate -group "📊 MEMORY Internal" -radix hexadecimal $MEMORY/*
add wave -noupdate -group "📊 WRITEBACK Internal" -radix hexadecimal $WRITEBACK/*

##################################################################################
#                           🎬 RUN SIMULATION                                    #
##################################################################################

# Update wave window
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ns} 0}

# Configure timeline
configure wave -timelineunits ns

# Run simulation
run 10000ns

# Zoom to fit all signals
wave zoom full

# Optional: Save waveform
# write format wave -window .main_pane.wave.interior.cs.body.pw.wf questa_waves.do

puts "═══════════════════════════════════════════════════════════════════"
puts "  Level RISC-V Debug Waveform Loaded Successfully!"
puts "═══════════════════════════════════════════════════════════════════"
puts "  Quick Tips:"
puts "    - Use 'run 1000ns' to run more simulation"
puts "    - Use 'wave zoom range 0ns 100ns' to zoom"
puts "    - Click group headers to expand/collapse"
puts "═══════════════════════════════════════════════════════════════════"
