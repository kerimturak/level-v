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

# Safe add-wave wrapper: in batch/non-GUI runs some wave commands fail
# so use this wrapper to catch and log errors without aborting the script.
proc aw {args} {
	if {[catch {eval add $args} err]} {
		puts "WARN: add wave failed: $err"
	}
}

# Wrap generic 'add' command so 'add wave' or other add-* calls
# won't abort the script in non-GUI/batch mode.
if {[llength [info commands add]] > 0} {
	rename add _add
	proc add {args} {
		# If the add call requests a divider/separator, skip it (user prefers no separators)
		foreach a $args {
			if {[string match *divider* $a]} {
				return
			}
		}
		if {[catch {eval _add $args} err]} {
			puts "WARN: add failed: $err"
		}
	}
}

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

# Also add full hierarchical tree for the testbench and key modules so
# the Wave window shows actual nested hierarchy instead of flat groups.
# Uses the safe wrapper `aw` to avoid failing in batch mode.
aw -noupdate -recursive $TB
aw -noupdate -recursive $WRAPPER
aw -noupdate -recursive $CPU

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

##################################################################################
#                              TESTBENCH                                         #
##################################################################################
add wave -noupdate -divider -height 20 {=============== TESTBENCH ===============}

add wave -noupdate -group "TB_WRAPPER" -group "Inputs" -color Gold $TB/clk_i
add wave -noupdate -group "TB_WRAPPER" -group "Inputs" -color Orange $TB/rst_ni
add wave -noupdate -group "TB_WRAPPER" -group "Inputs" $TB/prog_rx_i
add wave -noupdate -group "TB_WRAPPER" -group "Inputs" $TB/uart0_rx_i
add wave -noupdate -group "TB_WRAPPER" -group "Inputs" $TB/spi0_miso_i
add wave -noupdate -group "TB_WRAPPER" -group "Inputs" -radix hexadecimal $TB/gpio_i
add wave -noupdate -group "TB_WRAPPER" -group "Inputs" -radix hexadecimal $TB/ext_irq_i

add wave -noupdate -group "TB_WRAPPER" -group "Outputs" $TB/prog_mode_o
add wave -noupdate -group "TB_WRAPPER" -group "Outputs" $TB/uart0_tx_o
add wave -noupdate -group "TB_WRAPPER" -group "Outputs" $TB/spi0_sclk_o
add wave -noupdate -group "TB_WRAPPER" -group "Outputs" $TB/spi0_mosi_o
add wave -noupdate -group "TB_WRAPPER" -group "Outputs" -radix hexadecimal $TB/spi0_ss_o
add wave -noupdate -group "TB_WRAPPER" -group "Outputs" -radix hexadecimal $TB/gpio_o
add wave -noupdate -group "TB_WRAPPER" -group "Outputs" -radix hexadecimal $TB/gpio_oe_o
add wave -noupdate -group "TB_WRAPPER" -group "Outputs" -radix hexadecimal $TB/status_led_o

add wave -noupdate -group "TB_WRAPPER" -group "Bidirectional" $TB/i2c0_sda_io
add wave -noupdate -group "TB_WRAPPER" -group "Bidirectional" $TB/i2c0_scl_io

##################################################################################
#                              CERES_WRAPPER                                     #
##################################################################################
add wave -noupdate -divider -height 20 {=============== CERES_WRAPPER ===============}

add wave -noupdate -group "CERES_WRAPPER" -group "Inputs" -color Gold $WRAPPER/clk_i
add wave -noupdate -group "CERES_WRAPPER" -group "Inputs" -color Orange $WRAPPER/rst_ni
add wave -noupdate -group "CERES_WRAPPER" -group "Inputs" $WRAPPER/uart0_rx_i
add wave -noupdate -group "CERES_WRAPPER" -group "Inputs" $WRAPPER/prog_rx_i
add wave -noupdate -group "CERES_WRAPPER" -group "Inputs" $WRAPPER/spi0_miso_i
add wave -noupdate -group "CERES_WRAPPER" -group "Inputs" -radix hexadecimal $WRAPPER/gpio_i
add wave -noupdate -group "CERES_WRAPPER" -group "Inputs" -radix hexadecimal $WRAPPER/ext_irq_i

add wave -noupdate -group "CERES_WRAPPER" -group "Outputs" $WRAPPER/uart0_tx_o
add wave -noupdate -group "CERES_WRAPPER" -group "Outputs" $WRAPPER/prog_mode_o
add wave -noupdate -group "CERES_WRAPPER" -group "Outputs" $WRAPPER/spi0_sclk_o
add wave -noupdate -group "CERES_WRAPPER" -group "Outputs" $WRAPPER/spi0_mosi_o
add wave -noupdate -group "CERES_WRAPPER" -group "Outputs" -radix hexadecimal $WRAPPER/spi0_ss_o
add wave -noupdate -group "CERES_WRAPPER" -group "Outputs" -radix hexadecimal $WRAPPER/gpio_o
add wave -noupdate -group "CERES_WRAPPER" -group "Outputs" -radix hexadecimal $WRAPPER/gpio_oe_o
add wave -noupdate -group "CERES_WRAPPER" -group "Outputs" -radix hexadecimal $WRAPPER/status_led_o

add wave -noupdate -group "CERES_WRAPPER" -group "Internal" -radix hexadecimal $WRAPPER/cpu_mem_req
add wave -noupdate -group "CERES_WRAPPER" -group "Internal" -radix hexadecimal $WRAPPER/cpu_mem_res
add wave -noupdate -group "CERES_WRAPPER" -group "Internal" $WRAPPER/sys_rst_n
add wave -noupdate -group "CERES_WRAPPER" -group "Internal" $WRAPPER/prog_reset
add wave -noupdate -group "CERES_WRAPPER" -group "Internal" -radix hexadecimal $WRAPPER/wb_cpu_m
add wave -noupdate -group "CERES_WRAPPER" -group "Internal" -radix hexadecimal $WRAPPER/wb_cpu_s
add wave -noupdate -group "CERES_WRAPPER" -group "Internal" $WRAPPER/timer_irq
add wave -noupdate -group "CERES_WRAPPER" -group "Internal" $WRAPPER/sw_irq

##################################################################################
#                              WRAPPER_RAM                                       #
##################################################################################
add wave -noupdate -divider -height 20 {=============== WRAPPER_RAM ===============}

add wave -noupdate -group "WRAPPER_RAM" -group "Inputs" -color Gold $MAIN_RAM/clk_i
add wave -noupdate -group "WRAPPER_RAM" -group "Inputs" -color Orange $MAIN_RAM/rst_ni
add wave -noupdate -group "WRAPPER_RAM" -group "Inputs" -radix hexadecimal $MAIN_RAM/addr_i
add wave -noupdate -group "WRAPPER_RAM" -group "Inputs" -radix hexadecimal $MAIN_RAM/wdata_i
add wave -noupdate -group "WRAPPER_RAM" -group "Inputs" -radix hexadecimal $MAIN_RAM/wstrb_i
add wave -noupdate -group "WRAPPER_RAM" -group "Inputs" $MAIN_RAM/rd_en_i
add wave -noupdate -group "WRAPPER_RAM" -group "Inputs" $MAIN_RAM/ram_prog_rx_i

add wave -noupdate -group "WRAPPER_RAM" -group "Outputs" -radix hexadecimal $MAIN_RAM/rdata_o
add wave -noupdate -group "WRAPPER_RAM" -group "Outputs" $MAIN_RAM/system_reset_o
add wave -noupdate -group "WRAPPER_RAM" -group "Outputs" $MAIN_RAM/prog_mode_led_o

add wave -noupdate -group "WRAPPER_RAM" -group "Internal" -radix hexadecimal $MAIN_RAM/*

##################################################################################
#                              UART                                              #
##################################################################################
add wave -noupdate -divider -height 20 {=============== UART ===============}

add wave -noupdate -group "UART" -group "Inputs" -color Gold $UART/clk_i
add wave -noupdate -group "UART" -group "Inputs" -color Orange $UART/rst_ni
add wave -noupdate -group "UART" -group "Inputs" $UART/stb_i
add wave -noupdate -group "UART" -group "Inputs" -radix hexadecimal $UART/adr_i
add wave -noupdate -group "UART" -group "Inputs" -radix hexadecimal $UART/byte_sel_i
add wave -noupdate -group "UART" -group "Inputs" $UART/we_i
add wave -noupdate -group "UART" -group "Inputs" -radix hexadecimal $UART/dat_i
add wave -noupdate -group "UART" -group "Inputs" $UART/uart_rx_i

add wave -noupdate -group "UART" -group "Outputs" -radix hexadecimal $UART/dat_o
add wave -noupdate -group "UART" -group "Outputs" $UART/uart_tx_o

add wave -noupdate -group "UART" -group "Internal" -radix hexadecimal $UART/baud_div
add wave -noupdate -group "UART" -group "Internal" $UART/tx_en
add wave -noupdate -group "UART" -group "Internal" $UART/tx_full
add wave -noupdate -group "UART" -group "Internal" $UART/tx_empty
add wave -noupdate -group "UART" -group "Internal" $UART/tx_we
add wave -noupdate -group "UART" -group "Internal" $UART/rx_en
add wave -noupdate -group "UART" -group "Internal" -radix hexadecimal $UART/dout
add wave -noupdate -group "UART" -group "Internal" $UART/rx_full
add wave -noupdate -group "UART" -group "Internal" $UART/rx_empty
add wave -noupdate -group "UART" -group "Internal" $UART/rx_re

# UART_TX Submodule
add wave -noupdate -group "UART_TX" -group "Inputs" -color Gold $UART_TX/clk_i
add wave -noupdate -group "UART_TX" -group "Inputs" -color Orange $UART_TX/rst_ni
add wave -noupdate -group "UART_TX" -group "Inputs" -radix hexadecimal $UART_TX/baud_div_i
add wave -noupdate -group "UART_TX" -group "Inputs" $UART_TX/tx_we_i
add wave -noupdate -group "UART_TX" -group "Inputs" $UART_TX/tx_en_i
add wave -noupdate -group "UART_TX" -group "Inputs" -radix hexadecimal $UART_TX/din_i

add wave -noupdate -group "UART_TX" -group "Outputs" $UART_TX/full_o
add wave -noupdate -group "UART_TX" -group "Outputs" $UART_TX/empty_o
add wave -noupdate -group "UART_TX" -group "Outputs" $UART_TX/tx_bit_o

add wave -noupdate -group "UART_TX" -group "Internal" $UART_TX/state
add wave -noupdate -group "UART_TX" -group "Internal" -radix hexadecimal $UART_TX/data
add wave -noupdate -group "UART_TX" -group "Internal" -radix hexadecimal $UART_TX/frame
add wave -noupdate -group "UART_TX" -group "Internal" -radix unsigned $UART_TX/bit_counter
add wave -noupdate -group "UART_TX" -group "Internal" -radix unsigned $UART_TX/baud_counter
add wave -noupdate -group "UART_TX" -group "Internal" $UART_TX/baud_clk

# UART_RX Submodule
add wave -noupdate -group "UART_RX" -group "Inputs" -color Gold $UART_RX/clk_i
add wave -noupdate -group "UART_RX" -group "Inputs" -color Orange $UART_RX/rst_ni
add wave -noupdate -group "UART_RX" -group "Inputs" -radix hexadecimal $UART_RX/baud_div_i
add wave -noupdate -group "UART_RX" -group "Inputs" $UART_RX/rx_re_i
add wave -noupdate -group "UART_RX" -group "Inputs" $UART_RX/rx_en_i
add wave -noupdate -group "UART_RX" -group "Inputs" $UART_RX/rx_bit_i

add wave -noupdate -group "UART_RX" -group "Outputs" -radix hexadecimal $UART_RX/dout_o
add wave -noupdate -group "UART_RX" -group "Outputs" $UART_RX/full_o
add wave -noupdate -group "UART_RX" -group "Outputs" $UART_RX/empty_o

add wave -noupdate -group "UART_RX" -group "Internal" $UART_RX/state
add wave -noupdate -group "UART_RX" -group "Internal" -radix hexadecimal $UART_RX/data
add wave -noupdate -group "UART_RX" -group "Internal" -radix unsigned $UART_RX/bit_counter
add wave -noupdate -group "UART_RX" -group "Internal" -radix unsigned $UART_RX/baud_counter
add wave -noupdate -group "UART_RX" -group "Internal" $UART_RX/baud_clk

##################################################################################
#                              WISHBONE BUS                                      #
##################################################################################
add wave -noupdate -divider -height 20 {=============== WISHBONE BUS ===============}

# WB_MASTER_BRIDGE
add wave -noupdate -group "WB_MASTER" -group "Inputs" -color Gold $WB_MASTER/clk_i
add wave -noupdate -group "WB_MASTER" -group "Inputs" -color Orange $WB_MASTER/rst_ni
add wave -noupdate -group "WB_MASTER" -group "Inputs" -radix hexadecimal $WB_MASTER/iomem_req_i
add wave -noupdate -group "WB_MASTER" -group "Inputs" -radix hexadecimal $WB_MASTER/wb_s_i

add wave -noupdate -group "WB_MASTER" -group "Outputs" -radix hexadecimal $WB_MASTER/iomem_res_o
add wave -noupdate -group "WB_MASTER" -group "Outputs" -radix hexadecimal $WB_MASTER/wb_m_o

add wave -noupdate -group "WB_MASTER" -group "Internal" $WB_MASTER/state_q
add wave -noupdate -group "WB_MASTER" -group "Internal" -radix hexadecimal $WB_MASTER/addr_q
add wave -noupdate -group "WB_MASTER" -group "Internal" -radix hexadecimal $WB_MASTER/wdata_q
add wave -noupdate -group "WB_MASTER" -group "Internal" -radix hexadecimal $WB_MASTER/rdata_q
add wave -noupdate -group "WB_MASTER" -group "Internal" -radix unsigned $WB_MASTER/beat_cnt_q
add wave -noupdate -group "WB_MASTER" -group "Internal" $WB_MASTER/write_q
add wave -noupdate -group "WB_MASTER" -group "Internal" $WB_MASTER/uncached_q

# WB_INTERCONNECT
add wave -noupdate -group "WB_INTERCONNECT" -group "Inputs" -color Gold $WB_INTERCON/clk_i
add wave -noupdate -group "WB_INTERCONNECT" -group "Inputs" -color Orange $WB_INTERCON/rst_ni
add wave -noupdate -group "WB_INTERCONNECT" -group "Inputs" -radix hexadecimal $WB_INTERCON/wb_m_i
add wave -noupdate -group "WB_INTERCONNECT" -group "Inputs" -radix hexadecimal $WB_INTERCON/wb_s_i

add wave -noupdate -group "WB_INTERCONNECT" -group "Outputs" -radix hexadecimal $WB_INTERCON/wb_s_o
add wave -noupdate -group "WB_INTERCONNECT" -group "Outputs" -radix hexadecimal $WB_INTERCON/wb_m_o

add wave -noupdate -group "WB_INTERCONNECT" -group "Internal" $WB_INTERCON/slave_sel
add wave -noupdate -group "WB_INTERCONNECT" -group "Internal" $WB_INTERCON/addr_valid
add wave -noupdate -group "WB_INTERCONNECT" -group "Internal" -radix unsigned $WB_INTERCON/active_slave_q
add wave -noupdate -group "WB_INTERCONNECT" -group "Internal" $WB_INTERCON/req_pending_q

# WB_CLINT_SLAVE
add wave -noupdate -group "WB_CLINT" -group "Inputs" -color Gold $WB_CLINT/clk_i
add wave -noupdate -group "WB_CLINT" -group "Inputs" -color Orange $WB_CLINT/rst_ni
add wave -noupdate -group "WB_CLINT" -group "Inputs" -radix hexadecimal $WB_CLINT/wb_m_i

add wave -noupdate -group "WB_CLINT" -group "Outputs" -radix hexadecimal $WB_CLINT/wb_s_o
add wave -noupdate -group "WB_CLINT" -group "Outputs" $WB_CLINT/timer_irq_o
add wave -noupdate -group "WB_CLINT" -group "Outputs" $WB_CLINT/sw_irq_o

add wave -noupdate -group "WB_CLINT" -group "Internal" -radix hexadecimal $WB_CLINT/mtime_q
add wave -noupdate -group "WB_CLINT" -group "Internal" -radix hexadecimal $WB_CLINT/mtimecmp_q
add wave -noupdate -group "WB_CLINT" -group "Internal" $WB_CLINT/msip_q
add wave -noupdate -group "WB_CLINT" -group "Internal" $WB_CLINT/req_valid
add wave -noupdate -group "WB_CLINT" -group "Internal" -radix hexadecimal $WB_CLINT/reg_offset

# WB_PBUS_SLAVE
add wave -noupdate -group "WB_PBUS" -group "Inputs" -color Gold $WB_PBUS/clk_i
add wave -noupdate -group "WB_PBUS" -group "Inputs" -color Orange $WB_PBUS/rst_ni
add wave -noupdate -group "WB_PBUS" -group "Inputs" -radix hexadecimal $WB_PBUS/wb_m_i
add wave -noupdate -group "WB_PBUS" -group "Inputs" -radix hexadecimal $WB_PBUS/pbus_rdata_i
add wave -noupdate -group "WB_PBUS" -group "Inputs" $WB_PBUS/pbus_ready_i

add wave -noupdate -group "WB_PBUS" -group "Outputs" -radix hexadecimal $WB_PBUS/wb_s_o
add wave -noupdate -group "WB_PBUS" -group "Outputs" -radix hexadecimal $WB_PBUS/pbus_addr_o
add wave -noupdate -group "WB_PBUS" -group "Outputs" -radix hexadecimal $WB_PBUS/pbus_wdata_o
add wave -noupdate -group "WB_PBUS" -group "Outputs" -radix hexadecimal $WB_PBUS/pbus_wstrb_o
add wave -noupdate -group "WB_PBUS" -group "Outputs" $WB_PBUS/pbus_valid_o
add wave -noupdate -group "WB_PBUS" -group "Outputs" $WB_PBUS/pbus_we_o

add wave -noupdate -group "WB_PBUS" -group "Internal" $WB_PBUS/req_valid
add wave -noupdate -group "WB_PBUS" -group "Internal" $WB_PBUS/req_we

##################################################################################
#                              CPU                                               #
##################################################################################
add wave -noupdate -divider -height 20 {=============== CPU ===============}

add wave -noupdate -group "CPU" -group "Inputs" -color Gold $CPU/clk_i
add wave -noupdate -group "CPU" -group "Inputs" -color Orange $CPU/rst_ni
add wave -noupdate -group "CPU" -group "Inputs" -radix hexadecimal $CPU/iomem_res_i

add wave -noupdate -group "CPU" -group "Outputs" -radix hexadecimal $CPU/iomem_req_o

add wave -noupdate -group "CPU" -group "Pipeline Registers" -radix hexadecimal $CPU/pipe1
add wave -noupdate -group "CPU" -group "Pipeline Registers" -radix hexadecimal $CPU/pipe2
add wave -noupdate -group "CPU" -group "Pipeline Registers" -radix hexadecimal $CPU/pipe3
add wave -noupdate -group "CPU" -group "Pipeline Registers" -radix hexadecimal $CPU/pipe4

add wave -noupdate -group "CPU" -group "Stall/Flush Control" $CPU/stall_cause
add wave -noupdate -group "CPU" -group "Stall/Flush Control" $CPU/fe_imiss_stall
add wave -noupdate -group "CPU" -group "Stall/Flush Control" $CPU/me_dmiss_stall
add wave -noupdate -group "CPU" -group "Stall/Flush Control" $CPU/ex_alu_stall
add wave -noupdate -group "CPU" -group "Stall/Flush Control" $CPU/me_fencei_stall
add wave -noupdate -group "CPU" -group "Stall/Flush Control" $CPU/de_flush
add wave -noupdate -group "CPU" -group "Stall/Flush Control" $CPU/ex_flush
add wave -noupdate -group "CPU" -group "Stall/Flush Control" $CPU/fencei_flush
add wave -noupdate -group "CPU" -group "Stall/Flush Control" $CPU/priority_flush

add wave -noupdate -group "CPU" -group "Exception Handling" $CPU/trap_active
add wave -noupdate -group "CPU" -group "Exception Handling" $CPU/fe_trap_active
add wave -noupdate -group "CPU" -group "Exception Handling" $CPU/de_trap_active
add wave -noupdate -group "CPU" -group "Exception Handling" $CPU/excp_mask
add wave -noupdate -group "CPU" -group "Exception Handling" -radix hexadecimal $CPU/trap_tval
add wave -noupdate -group "CPU" -group "Exception Handling" $CPU/fe_exc_type
add wave -noupdate -group "CPU" -group "Exception Handling" $CPU/de_exc_type
add wave -noupdate -group "CPU" -group "Exception Handling" $CPU/ex_exc_type
add wave -noupdate -group "CPU" -group "Exception Handling" $CPU/ex_alu_exc_type
add wave -noupdate -group "CPU" -group "Exception Handling" -radix hexadecimal $CPU/ex_trap_cause
add wave -noupdate -group "CPU" -group "Exception Handling" -radix hexadecimal $CPU/ex_trap_mepc
add wave -noupdate -group "CPU" -group "Exception Handling" -radix hexadecimal $CPU/ex_mtvec

add wave -noupdate -group "CPU" -group "Branch Prediction" $CPU/ex_spec_hit
add wave -noupdate -group "CPU" -group "Branch Prediction" $CPU/ex_pc_sel
add wave -noupdate -group "CPU" -group "Branch Prediction" -radix hexadecimal $CPU/ex_pc_target
add wave -noupdate -group "CPU" -group "Branch Prediction" -radix hexadecimal $CPU/ex_pc_target_last
add wave -noupdate -group "CPU" -group "Branch Prediction" $CPU/fe_spec

add wave -noupdate -group "CPU" -group "Data Request" -radix hexadecimal $CPU/ex_data_req
add wave -noupdate -group "CPU" -group "Data Request" -radix hexadecimal $CPU/me_data_req

add wave -noupdate -group "CPU" -group "Forwarding" $CPU/de_fwd_a
add wave -noupdate -group "CPU" -group "Forwarding" $CPU/de_fwd_b
add wave -noupdate -group "CPU" -group "Forwarding" $CPU/ex_fwd_a
add wave -noupdate -group "CPU" -group "Forwarding" $CPU/ex_fwd_b

##################################################################################
#                              STAGE 1: FETCH                                    #
##################################################################################
add wave -noupdate -divider -height 20 {=============== FETCH ===============}

add wave -noupdate -group "FETCH" -group "Inputs" -color Gold $FETCH/clk_i
add wave -noupdate -group "FETCH" -group "Inputs" -color Orange $FETCH/rst_ni
add wave -noupdate -group "FETCH" -group "Inputs" $FETCH/stall_i
add wave -noupdate -group "FETCH" -group "Inputs" $FETCH/flush_i
add wave -noupdate -group "FETCH" -group "Inputs" -radix hexadecimal $FETCH/flush_pc_i
add wave -noupdate -group "FETCH" -group "Inputs" -radix hexadecimal $FETCH/lx_ires_i
add wave -noupdate -group "FETCH" -group "Inputs" -radix hexadecimal $FETCH/pc_target_i
add wave -noupdate -group "FETCH" -group "Inputs" $FETCH/spec_hit_i
add wave -noupdate -group "FETCH" -group "Inputs" -radix hexadecimal $FETCH/ex_mtvec_i
add wave -noupdate -group "FETCH" -group "Inputs" $FETCH/trap_active_i
add wave -noupdate -group "FETCH" -group "Inputs" $FETCH/misa_c_i
add wave -noupdate -group "FETCH" -group "Inputs" -radix hexadecimal $FETCH/tdata1_i
add wave -noupdate -group "FETCH" -group "Inputs" -radix hexadecimal $FETCH/tdata2_i
add wave -noupdate -group "FETCH" -group "Inputs" -radix hexadecimal $FETCH/tcontrol_i
add wave -noupdate -group "FETCH" -group "Inputs" $FETCH/de_info_i
add wave -noupdate -group "FETCH" -group "Inputs" $FETCH/ex_info_i

add wave -noupdate -group "FETCH" -group "Outputs" $FETCH/spec_o
add wave -noupdate -group "FETCH" -group "Outputs" -radix hexadecimal $FETCH/lx_ireq_o
add wave -noupdate -group "FETCH" -group "Outputs" -radix hexadecimal $FETCH/pc_o
add wave -noupdate -group "FETCH" -group "Outputs" -radix hexadecimal $FETCH/pc_incr_o
add wave -noupdate -group "FETCH" -group "Outputs" -radix hexadecimal $FETCH/inst_o
add wave -noupdate -group "FETCH" -group "Outputs" $FETCH/imiss_stall_o
add wave -noupdate -group "FETCH" -group "Outputs" $FETCH/exc_type_o
add wave -noupdate -group "FETCH" -group "Outputs" $FETCH/instr_type_o

add wave -noupdate -group "FETCH" -group "Internal" -radix hexadecimal $FETCH/pc
add wave -noupdate -group "FETCH" -group "Internal" -radix hexadecimal $FETCH/pc_next
add wave -noupdate -group "FETCH" -group "Internal" $FETCH/pc_en
add wave -noupdate -group "FETCH" -group "Internal" $FETCH/fetch_valid
add wave -noupdate -group "FETCH" -group "Internal" $FETCH/uncached
add wave -noupdate -group "FETCH" -group "Internal" $FETCH/grand
add wave -noupdate -group "FETCH" -group "Internal" $FETCH/illegal_instr
add wave -noupdate -group "FETCH" -group "Internal" $FETCH/is_comp

##################################################################################
#                              FETCH SUBMODULES                                  #
##################################################################################
add wave -noupdate -divider -height 15 {FETCH SUBMODULES}

# ICACHE
add wave -noupdate -group "ICACHE" -group "Inputs" -color Gold $ICACHE/clk_i
add wave -noupdate -group "ICACHE" -group "Inputs" -color Orange $ICACHE/rst_ni
add wave -noupdate -group "ICACHE" -group "Inputs" $ICACHE/flush_i
add wave -noupdate -group "ICACHE" -group "Inputs" -radix hexadecimal $ICACHE/cache_req_i
add wave -noupdate -group "ICACHE" -group "Inputs" -radix hexadecimal $ICACHE/lowX_res_i

add wave -noupdate -group "ICACHE" -group "Outputs" -radix hexadecimal $ICACHE/cache_res_o
add wave -noupdate -group "ICACHE" -group "Outputs" -radix hexadecimal $ICACHE/lowX_req_o
add wave -noupdate -group "ICACHE" -group "Outputs" $ICACHE/fencei_stall_o

add wave -noupdate -group "ICACHE" -group "Internal" -radix hexadecimal $ICACHE/*

# ALIGN_BUFFER
add wave -noupdate -group "ALIGN_BUFFER" -group "Inputs" -color Gold $ALIGN_BUFFER/clk_i
add wave -noupdate -group "ALIGN_BUFFER" -group "Inputs" -color Orange $ALIGN_BUFFER/rst_ni
add wave -noupdate -group "ALIGN_BUFFER" -group "Inputs" $ALIGN_BUFFER/flush_i
add wave -noupdate -group "ALIGN_BUFFER" -group "Inputs" -radix hexadecimal $ALIGN_BUFFER/buff_req_i
add wave -noupdate -group "ALIGN_BUFFER" -group "Inputs" -radix hexadecimal $ALIGN_BUFFER/lowX_res_i

add wave -noupdate -group "ALIGN_BUFFER" -group "Outputs" -radix hexadecimal $ALIGN_BUFFER/buff_res_o
add wave -noupdate -group "ALIGN_BUFFER" -group "Outputs" -radix hexadecimal $ALIGN_BUFFER/lowX_req_o

add wave -noupdate -group "ALIGN_BUFFER" -group "Internal" -radix hexadecimal $ALIGN_BUFFER/*

# COMPRESSED_DECODER
add wave -noupdate -group "COMPRESSED_DECODER" -group "Inputs" -radix hexadecimal $COMP_DECODER/instr_i
add wave -noupdate -group "COMPRESSED_DECODER" -group "Outputs" -radix hexadecimal $COMP_DECODER/instr_o
add wave -noupdate -group "COMPRESSED_DECODER" -group "Outputs" $COMP_DECODER/is_compressed_o
add wave -noupdate -group "COMPRESSED_DECODER" -group "Outputs" $COMP_DECODER/illegal_instr_o
add wave -noupdate -group "COMPRESSED_DECODER" -group "Internal" -radix hexadecimal $COMP_DECODER/*

# GSHARE Branch Predictor
add wave -noupdate -group "GSHARE_BP" -group "Inputs" -color Gold $GSHARE/clk_i
add wave -noupdate -group "GSHARE_BP" -group "Inputs" -color Orange $GSHARE/rst_ni
add wave -noupdate -group "GSHARE_BP" -group "Inputs" -radix hexadecimal $GSHARE/pc_i
add wave -noupdate -group "GSHARE_BP" -group "Inputs" $GSHARE/de_info_i
add wave -noupdate -group "GSHARE_BP" -group "Inputs" $GSHARE/ex_info_i

add wave -noupdate -group "GSHARE_BP" -group "Outputs" $GSHARE/spec_o

add wave -noupdate -group "GSHARE_BP" -group "Internal" -radix hexadecimal $GSHARE/*

# RAS (Return Address Stack)
add wave -noupdate -group "RAS" -group "Inputs" -color Gold $RAS/clk_i
add wave -noupdate -group "RAS" -group "Inputs" -color Orange $RAS/rst_ni
add wave -noupdate -group "RAS" -group "Inputs" -radix hexadecimal $RAS/restore_i
add wave -noupdate -group "RAS" -group "Inputs" $RAS/req_valid_i
add wave -noupdate -group "RAS" -group "Inputs" $RAS/j_type_i
add wave -noupdate -group "RAS" -group "Inputs" $RAS/jr_type_i
add wave -noupdate -group "RAS" -group "Inputs" -radix hexadecimal $RAS/rd_addr_i
add wave -noupdate -group "RAS" -group "Inputs" -radix hexadecimal $RAS/r1_addr_i
add wave -noupdate -group "RAS" -group "Inputs" -radix hexadecimal $RAS/return_addr_i

add wave -noupdate -group "RAS" -group "Outputs" -radix hexadecimal $RAS/popped_o

add wave -noupdate -group "RAS" -group "Internal" -radix hexadecimal $RAS/*

# Instruction PMA
add wave -noupdate -group "IPMA" -group "Inputs" -radix hexadecimal $IPMA/addr_i
add wave -noupdate -group "IPMA" -group "Outputs" $IPMA/uncached_o
add wave -noupdate -group "IPMA" -group "Outputs" $IPMA/memregion_o
add wave -noupdate -group "IPMA" -group "Outputs" $IPMA/grand_o
add wave -noupdate -group "IPMA" -group "Internal" -radix hexadecimal $IPMA/*

##################################################################################
#                              STAGE 2: DECODE                                   #
##################################################################################
add wave -noupdate -divider -height 20 {=============== DECODE ===============}

add wave -noupdate -group "DECODE" -group "Inputs" -color Gold $DECODE/clk_i
add wave -noupdate -group "DECODE" -group "Inputs" -color Orange $DECODE/rst_ni
add wave -noupdate -group "DECODE" -group "Inputs" -radix hexadecimal $DECODE/inst_i
add wave -noupdate -group "DECODE" -group "Inputs" $DECODE/fwd_a_i
add wave -noupdate -group "DECODE" -group "Inputs" $DECODE/fwd_b_i
add wave -noupdate -group "DECODE" -group "Inputs" -radix hexadecimal $DECODE/wb_data_i
add wave -noupdate -group "DECODE" -group "Inputs" -radix unsigned $DECODE/rd_addr_i
add wave -noupdate -group "DECODE" -group "Inputs" $DECODE/rf_rw_en_i
add wave -noupdate -group "DECODE" -group "Inputs" $DECODE/instr_type_i

add wave -noupdate -group "DECODE" -group "Outputs" -radix hexadecimal $DECODE/r1_data_o
add wave -noupdate -group "DECODE" -group "Outputs" -radix hexadecimal $DECODE/r2_data_o
add wave -noupdate -group "DECODE" -group "Outputs" $DECODE/ctrl_o
add wave -noupdate -group "DECODE" -group "Outputs" -radix hexadecimal $DECODE/imm_o
add wave -noupdate -group "DECODE" -group "Outputs" $DECODE/exc_type_o

add wave -noupdate -group "DECODE" -group "Internal" -radix hexadecimal $DECODE/r1_data
add wave -noupdate -group "DECODE" -group "Internal" -radix hexadecimal $DECODE/r2_data

##################################################################################
#                              DECODE SUBMODULES                                 #
##################################################################################
add wave -noupdate -divider -height 15 {DECODE SUBMODULES}

# CONTROL_UNIT
add wave -noupdate -group "CONTROL_UNIT" -radix hexadecimal $CTRL_UNIT/*

# REG_FILE
add wave -noupdate -group "REG_FILE" -group "Inputs" -color Gold $REG_FILE/clk_i
add wave -noupdate -group "REG_FILE" -group "Inputs" -color Orange $REG_FILE/rst_ni
add wave -noupdate -group "REG_FILE" -group "Inputs" $REG_FILE/rw_en_i
add wave -noupdate -group "REG_FILE" -group "Inputs" -radix unsigned $REG_FILE/r1_addr_i
add wave -noupdate -group "REG_FILE" -group "Inputs" -radix unsigned $REG_FILE/r2_addr_i
add wave -noupdate -group "REG_FILE" -group "Inputs" -radix unsigned $REG_FILE/waddr_i
add wave -noupdate -group "REG_FILE" -group "Inputs" -radix hexadecimal $REG_FILE/wdata_i

add wave -noupdate -group "REG_FILE" -group "Outputs" -radix hexadecimal $REG_FILE/r1_data_o
add wave -noupdate -group "REG_FILE" -group "Outputs" -radix hexadecimal $REG_FILE/r2_data_o

add wave -noupdate -group "REG_FILE" -group "Registers" -radix hexadecimal $REG_FILE/registers

# EXTEND
add wave -noupdate -group "EXTEND" -radix hexadecimal $EXTEND/*

##################################################################################
#                              STAGE 3: EXECUTE                                  #
##################################################################################
add wave -noupdate -divider -height 20 {=============== EXECUTE ===============}

add wave -noupdate -group "EXECUTE" -group "Inputs" -color Gold $EXECUTE/clk_i
add wave -noupdate -group "EXECUTE" -group "Inputs" -color Orange $EXECUTE/rst_ni
add wave -noupdate -group "EXECUTE" -group "Inputs" $EXECUTE/stall_i
add wave -noupdate -group "EXECUTE" -group "Inputs" $EXECUTE/fwd_a_i
add wave -noupdate -group "EXECUTE" -group "Inputs" $EXECUTE/fwd_b_i
add wave -noupdate -group "EXECUTE" -group "Inputs" -radix hexadecimal $EXECUTE/alu_result_i
add wave -noupdate -group "EXECUTE" -group "Inputs" -radix hexadecimal $EXECUTE/wb_data_i
add wave -noupdate -group "EXECUTE" -group "Inputs" -radix hexadecimal $EXECUTE/r1_data_i
add wave -noupdate -group "EXECUTE" -group "Inputs" -radix hexadecimal $EXECUTE/r2_data_i
add wave -noupdate -group "EXECUTE" -group "Inputs" $EXECUTE/alu_in1_sel_i
add wave -noupdate -group "EXECUTE" -group "Inputs" $EXECUTE/alu_in2_sel_i
add wave -noupdate -group "EXECUTE" -group "Inputs" $EXECUTE/rd_csr_i
add wave -noupdate -group "EXECUTE" -group "Inputs" $EXECUTE/wr_csr_i
add wave -noupdate -group "EXECUTE" -group "Inputs" -radix hexadecimal $EXECUTE/csr_idx_i
add wave -noupdate -group "EXECUTE" -group "Inputs" $EXECUTE/csr_or_data_i
add wave -noupdate -group "EXECUTE" -group "Inputs" $EXECUTE/trap_active_i
add wave -noupdate -group "EXECUTE" -group "Inputs" $EXECUTE/de_trap_active_i
add wave -noupdate -group "EXECUTE" -group "Inputs" -radix hexadecimal $EXECUTE/trap_cause_i
add wave -noupdate -group "EXECUTE" -group "Inputs" -radix hexadecimal $EXECUTE/trap_tval_i
add wave -noupdate -group "EXECUTE" -group "Inputs" -radix hexadecimal $EXECUTE/trap_mepc_i
add wave -noupdate -group "EXECUTE" -group "Inputs" -radix hexadecimal $EXECUTE/pc_i
add wave -noupdate -group "EXECUTE" -group "Inputs" -radix hexadecimal $EXECUTE/pc_incr_i
add wave -noupdate -group "EXECUTE" -group "Inputs" -radix hexadecimal $EXECUTE/imm_i
add wave -noupdate -group "EXECUTE" -group "Inputs" $EXECUTE/pc_sel_i
add wave -noupdate -group "EXECUTE" -group "Inputs" $EXECUTE/alu_ctrl_i
add wave -noupdate -group "EXECUTE" -group "Inputs" $EXECUTE/instr_type_i

add wave -noupdate -group "EXECUTE" -group "Outputs" -radix hexadecimal $EXECUTE/write_data_o
add wave -noupdate -group "EXECUTE" -group "Outputs" -radix hexadecimal $EXECUTE/pc_target_o
add wave -noupdate -group "EXECUTE" -group "Outputs" -radix hexadecimal $EXECUTE/alu_result_o
add wave -noupdate -group "EXECUTE" -group "Outputs" $EXECUTE/pc_sel_o
add wave -noupdate -group "EXECUTE" -group "Outputs" $EXECUTE/alu_stall_o
add wave -noupdate -group "EXECUTE" -group "Outputs" $EXECUTE/exc_type_o
add wave -noupdate -group "EXECUTE" -group "Outputs" -radix hexadecimal $EXECUTE/mtvec_o
add wave -noupdate -group "EXECUTE" -group "Outputs" $EXECUTE/misa_c_o
add wave -noupdate -group "EXECUTE" -group "Outputs" -radix hexadecimal $EXECUTE/tdata1_o
add wave -noupdate -group "EXECUTE" -group "Outputs" -radix hexadecimal $EXECUTE/tdata2_o
add wave -noupdate -group "EXECUTE" -group "Outputs" -radix hexadecimal $EXECUTE/tcontrol_o

add wave -noupdate -group "EXECUTE" -group "Internal" -radix hexadecimal $EXECUTE/data_a
add wave -noupdate -group "EXECUTE" -group "Internal" -radix hexadecimal $EXECUTE/operant_a
add wave -noupdate -group "EXECUTE" -group "Internal" -radix hexadecimal $EXECUTE/operant_b
add wave -noupdate -group "EXECUTE" -group "Internal" -radix hexadecimal $EXECUTE/alu_result
add wave -noupdate -group "EXECUTE" -group "Internal" -radix hexadecimal $EXECUTE/csr_rdata
add wave -noupdate -group "EXECUTE" -group "Internal" -radix hexadecimal $EXECUTE/mepc
add wave -noupdate -group "EXECUTE" -group "Internal" $EXECUTE/ex_zero
add wave -noupdate -group "EXECUTE" -group "Internal" $EXECUTE/ex_slt
add wave -noupdate -group "EXECUTE" -group "Internal" $EXECUTE/ex_sltu

##################################################################################
#                              EXECUTE SUBMODULES                                #
##################################################################################
add wave -noupdate -divider -height 15 {EXECUTE SUBMODULES}

# ALU
add wave -noupdate -group "ALU" -group "Inputs" -radix hexadecimal $ALU/alu_a_i
add wave -noupdate -group "ALU" -group "Inputs" -radix hexadecimal $ALU/alu_b_i
add wave -noupdate -group "ALU" -group "Inputs" $ALU/op_sel_i

add wave -noupdate -group "ALU" -group "Outputs" -radix hexadecimal $ALU/alu_o
add wave -noupdate -group "ALU" -group "Outputs" $ALU/zero_o
add wave -noupdate -group "ALU" -group "Outputs" $ALU/slt_o
add wave -noupdate -group "ALU" -group "Outputs" $ALU/sltu_o
add wave -noupdate -group "ALU" -group "Outputs" $ALU/alu_stall_o

add wave -noupdate -group "ALU" -group "Internal" -radix hexadecimal $ALU/*

# CSR_FILE
add wave -noupdate -group "CSR_FILE" -radix hexadecimal $CSR_FILE/*

##################################################################################
#                              STAGE 4: MEMORY                                   #
##################################################################################
add wave -noupdate -divider -height 20 {=============== MEMORY ===============}

add wave -noupdate -group "MEMORY" -group "Inputs" -color Gold $MEMORY/clk_i
add wave -noupdate -group "MEMORY" -group "Inputs" -color Orange $MEMORY/rst_ni
add wave -noupdate -group "MEMORY" -group "Inputs" $MEMORY/stall_i
add wave -noupdate -group "MEMORY" -group "Inputs" $MEMORY/fe_flush_cache_i
add wave -noupdate -group "MEMORY" -group "Inputs" -radix hexadecimal $MEMORY/lx_dres_i
add wave -noupdate -group "MEMORY" -group "Inputs" -radix hexadecimal $MEMORY/me_data_req_i
add wave -noupdate -group "MEMORY" -group "Inputs" -radix hexadecimal $MEMORY/ex_data_req_i

add wave -noupdate -group "MEMORY" -group "Outputs" -radix hexadecimal $MEMORY/lx_dreq_o
add wave -noupdate -group "MEMORY" -group "Outputs" -radix hexadecimal $MEMORY/me_data_o
add wave -noupdate -group "MEMORY" -group "Outputs" $MEMORY/dmiss_stall_o
add wave -noupdate -group "MEMORY" -group "Outputs" $MEMORY/fencei_stall_o

add wave -noupdate -group "MEMORY" -group "Internal" -radix hexadecimal $MEMORY/dcache_req
add wave -noupdate -group "MEMORY" -group "Internal" -radix hexadecimal $MEMORY/dcache_res
add wave -noupdate -group "MEMORY" -group "Internal" -radix hexadecimal $MEMORY/rd_data
add wave -noupdate -group "MEMORY" -group "Internal" $MEMORY/uncached
add wave -noupdate -group "MEMORY" -group "Internal" $MEMORY/mem_txn_active
add wave -noupdate -group "MEMORY" -group "Internal" $MEMORY/mem_req_fire
add wave -noupdate -group "MEMORY" -group "Internal" $MEMORY/req_changed

##################################################################################
#                              MEMORY SUBMODULES                                 #
##################################################################################
add wave -noupdate -divider -height 15 {MEMORY SUBMODULES}

# DCACHE
add wave -noupdate -group "DCACHE" -group "Inputs" -color Gold $DCACHE/clk_i
add wave -noupdate -group "DCACHE" -group "Inputs" -color Orange $DCACHE/rst_ni
add wave -noupdate -group "DCACHE" -group "Inputs" $DCACHE/flush_i
add wave -noupdate -group "DCACHE" -group "Inputs" -radix hexadecimal $DCACHE/cache_req_i
add wave -noupdate -group "DCACHE" -group "Inputs" -radix hexadecimal $DCACHE/lowX_res_i

add wave -noupdate -group "DCACHE" -group "Outputs" -radix hexadecimal $DCACHE/cache_res_o
add wave -noupdate -group "DCACHE" -group "Outputs" -radix hexadecimal $DCACHE/lowX_req_o
add wave -noupdate -group "DCACHE" -group "Outputs" $DCACHE/fencei_stall_o

add wave -noupdate -group "DCACHE" -group "Internal" -radix hexadecimal $DCACHE/*

# Data PMA
add wave -noupdate -group "DPMA" -group "Inputs" -radix hexadecimal $DPMA/addr_i
add wave -noupdate -group "DPMA" -group "Outputs" $DPMA/uncached_o
add wave -noupdate -group "DPMA" -group "Outputs" $DPMA/memregion_o
add wave -noupdate -group "DPMA" -group "Outputs" $DPMA/grand_o
add wave -noupdate -group "DPMA" -group "Internal" -radix hexadecimal $DPMA/*

##################################################################################
#                              STAGE 5: WRITEBACK                                #
##################################################################################
add wave -noupdate -divider -height 20 {=============== WRITEBACK ===============}

add wave -noupdate -group "WRITEBACK" -group "Inputs" -color Gold $WRITEBACK/clk_i
add wave -noupdate -group "WRITEBACK" -group "Inputs" -color Orange $WRITEBACK/rst_ni
add wave -noupdate -group "WRITEBACK" -group "Inputs" $WRITEBACK/stall_i
add wave -noupdate -group "WRITEBACK" -group "Inputs" $WRITEBACK/data_sel_i
add wave -noupdate -group "WRITEBACK" -group "Inputs" -radix hexadecimal $WRITEBACK/pc_incr_i
add wave -noupdate -group "WRITEBACK" -group "Inputs" -radix hexadecimal $WRITEBACK/pc_i
add wave -noupdate -group "WRITEBACK" -group "Inputs" -radix hexadecimal $WRITEBACK/alu_result_i
add wave -noupdate -group "WRITEBACK" -group "Inputs" -radix hexadecimal $WRITEBACK/read_data_i
add wave -noupdate -group "WRITEBACK" -group "Inputs" $WRITEBACK/rf_rw_en_i
add wave -noupdate -group "WRITEBACK" -group "Inputs" $WRITEBACK/fe_flush_cache_i

add wave -noupdate -group "WRITEBACK" -group "Outputs" $WRITEBACK/rf_rw_en_o
add wave -noupdate -group "WRITEBACK" -group "Outputs" -radix hexadecimal $WRITEBACK/wb_data_o

##################################################################################
#                              HAZARD_UNIT                                       #
##################################################################################
add wave -noupdate -divider -height 20 {=============== HAZARD_UNIT ===============}

add wave -noupdate -group "HAZARD_UNIT" -group "Inputs" -radix unsigned $HAZARD/r1_addr_de_i
add wave -noupdate -group "HAZARD_UNIT" -group "Inputs" -radix unsigned $HAZARD/r2_addr_de_i
add wave -noupdate -group "HAZARD_UNIT" -group "Inputs" -radix unsigned $HAZARD/r1_addr_ex_i
add wave -noupdate -group "HAZARD_UNIT" -group "Inputs" -radix unsigned $HAZARD/r2_addr_ex_i
add wave -noupdate -group "HAZARD_UNIT" -group "Inputs" -radix unsigned $HAZARD/rd_addr_ex_i
add wave -noupdate -group "HAZARD_UNIT" -group "Inputs" $HAZARD/pc_sel_ex_i
add wave -noupdate -group "HAZARD_UNIT" -group "Inputs" $HAZARD/rslt_sel_ex_0
add wave -noupdate -group "HAZARD_UNIT" -group "Inputs" -radix unsigned $HAZARD/rd_addr_me_i
add wave -noupdate -group "HAZARD_UNIT" -group "Inputs" $HAZARD/rf_rw_me_i
add wave -noupdate -group "HAZARD_UNIT" -group "Inputs" $HAZARD/rf_rw_wb_i
add wave -noupdate -group "HAZARD_UNIT" -group "Inputs" -radix unsigned $HAZARD/rd_addr_wb_i

add wave -noupdate -group "HAZARD_UNIT" -group "Outputs" $HAZARD/stall_fe_o
add wave -noupdate -group "HAZARD_UNIT" -group "Outputs" $HAZARD/stall_de_o
add wave -noupdate -group "HAZARD_UNIT" -group "Outputs" $HAZARD/flush_de_o
add wave -noupdate -group "HAZARD_UNIT" -group "Outputs" $HAZARD/flush_ex_o
add wave -noupdate -group "HAZARD_UNIT" -group "Outputs" $HAZARD/fwd_a_ex_o
add wave -noupdate -group "HAZARD_UNIT" -group "Outputs" $HAZARD/fwd_b_ex_o
add wave -noupdate -group "HAZARD_UNIT" -group "Outputs" $HAZARD/fwd_a_de_o
add wave -noupdate -group "HAZARD_UNIT" -group "Outputs" $HAZARD/fwd_b_de_o

add wave -noupdate -group "HAZARD_UNIT" -group "Internal" $HAZARD/lw_stall

##################################################################################
#                              MEMORY_ARBITER                                    #
##################################################################################
add wave -noupdate -divider -height 20 {=============== MEMORY_ARBITER ===============}

add wave -noupdate -group "MEMORY_ARBITER" -group "Inputs" -color Gold $ARBITER/clk_i
add wave -noupdate -group "MEMORY_ARBITER" -group "Inputs" -color Orange $ARBITER/rst_ni
add wave -noupdate -group "MEMORY_ARBITER" -group "Inputs" -radix hexadecimal $ARBITER/icache_req_i
add wave -noupdate -group "MEMORY_ARBITER" -group "Inputs" -radix hexadecimal $ARBITER/dcache_req_i
add wave -noupdate -group "MEMORY_ARBITER" -group "Inputs" -radix hexadecimal $ARBITER/iomem_res_i

add wave -noupdate -group "MEMORY_ARBITER" -group "Outputs" -radix hexadecimal $ARBITER/icache_res_o
add wave -noupdate -group "MEMORY_ARBITER" -group "Outputs" -radix hexadecimal $ARBITER/dcache_res_o
add wave -noupdate -group "MEMORY_ARBITER" -group "Outputs" -radix hexadecimal $ARBITER/iomem_req_o

add wave -noupdate -group "MEMORY_ARBITER" -group "Internal" $ARBITER/round
add wave -noupdate -group "MEMORY_ARBITER" -group "Internal" -radix hexadecimal $ARBITER/icache_req_reg
add wave -noupdate -group "MEMORY_ARBITER" -group "Internal" -radix hexadecimal $ARBITER/dcache_req_reg

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

##################################################################################
#                              RUN SIMULATION                                    #
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

puts "=================================================================="
puts "  CERES RISC-V Debug Waveform Loaded Successfully!"
puts "=================================================================="
puts "  Quick Tips:"
puts "    - Use 'run 1000ns' to run more simulation"
puts "    - Use 'wave zoom range 0ns 100ns' to zoom"
puts "    - Click group headers to expand/collapse"
puts "=================================================================="
