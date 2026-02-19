# ==============================================================
# CERES RISC-V SoC — SDC Constraint File (SKY130 / OpenLane)
# ==============================================================
# Target: sky130_fd_sc_hd  |  Clock: 33.3 MHz (30 ns period)
# This file is used as BASE_SDC_FILE, PNR_SDC_FILE, and
# SIGNOFF_SDC_FILE in config.tcl.
# ==============================================================

set_units -time ns

# ==============================================================
# 1. CLOCK DEFINITION
# ==============================================================
set CLK_PERIOD 30.0
set CLK_PORT   clk_i

create_clock [get_ports $CLK_PORT] \
    -name core_clk \
    -period $CLK_PERIOD \
    -waveform [list 0 [expr {$CLK_PERIOD / 2.0}]]

# ==============================================================
# 2. CLOCK UNCERTAINTY & TRANSITION
# ==============================================================
# Jitter + OCV: pre-CTS=0.25 ns is the OpenLane default.
# Post-CTS the flow re-annotates from SPEF, so this is fine.
set CLK_UNCERTAINTY 0.25
set CLK_TRANSITION  0.15

set_clock_uncertainty $CLK_UNCERTAINTY [get_clocks core_clk]
set_clock_transition  $CLK_TRANSITION  [get_clocks core_clk]

# ==============================================================
# 3. TIMING DERATE (OCV)
# ==============================================================
# ±5% derate — OpenLane default for on-chip variation modelling.
set DERATE 0.05
set_timing_derate -early [expr {1.0 - $DERATE}]
set_timing_derate -late  [expr {1.0 + $DERATE}]

# ==============================================================
# 4. I/O DELAY BUDGETS
# ==============================================================
# IO_PCT = fraction of clock period reserved for external path.
# OpenLane default is 0.2 (20%).  We use 25% for more margin.
set IO_PCT 0.25
set INPUT_DELAY  [expr {$CLK_PERIOD * $IO_PCT}]
set OUTPUT_DELAY [expr {$CLK_PERIOD * $IO_PCT}]

# Collect all inputs except clock and reset (async)
set clk_port_obj  [get_ports $CLK_PORT]
set all_in        [all_inputs]
set clk_idx       [lsearch $all_in $clk_port_obj]
set all_in_no_clk [lreplace $all_in $clk_idx $clk_idx]

# Remove reset (async, constrained separately)
set rst_port_obj     [get_ports rst_ni]
set rst_idx          [lsearch $all_in_no_clk $rst_port_obj]
set all_in_no_clk_rst [lreplace $all_in_no_clk $rst_idx $rst_idx]

set_input_delay  $INPUT_DELAY  -clock [get_clocks core_clk] $all_in_no_clk_rst
set_output_delay $OUTPUT_DELAY -clock [get_clocks core_clk] [all_outputs]

# ==============================================================
# 5. RESET CONSTRAINTS
# ==============================================================
# rst_ni is asynchronous active-low reset — no launch clock.
# Allow up to half the period for the reset deassertion path.
set_input_delay  [expr {$CLK_PERIOD * 0.5}] -clock [get_clocks core_clk] [get_ports rst_ni]
set_false_path -from [get_ports rst_ni]

# ==============================================================
# 6. MAX FANOUT & MAX TRANSITION
# ==============================================================
set_max_fanout 12 [current_design]

# Sky130 hd library typical max transition ~1.5 ns; we constrain
# to ~0.75 ns to leave headroom for the resizer.
set_max_transition 0.75 [current_design]

# ==============================================================
# 7. DRIVING CELL & OUTPUT LOAD
# ==============================================================
# Driving cell for all inputs: sky130_fd_sc_hd__buf_2 (pin X)
# This models the realistic drive strength of the external logic.
set_driving_cell -lib_cell sky130_fd_sc_hd__buf_2 -pin X $all_in_no_clk_rst

# Clock input driven by a stronger buffer
set_driving_cell -lib_cell sky130_fd_sc_hd__buf_8 -pin X $clk_port_obj

# Output load: 33 fF (= 0.033 pF) — typical ASIC-to-pad estimate
set_load 0.033 [all_outputs]

# ==============================================================
# 8. FALSE PATHS — ASYNCHRONOUS INTERFACES
# ==============================================================
# UART is asynchronous (baud-rate domain) — no timing relationship
# with core_clk edges.
set_false_path -from [get_ports uart0_rx_i]
set_false_path -to   [get_ports uart0_tx_o]
set_false_path -from [get_ports uart1_rx_i]
set_false_path -to   [get_ports uart1_tx_o]

# Programming UART (async)
set_false_path -from [get_ports prog_rx_i]
set_false_path -to   [get_ports prog_mode_o]

# External interrupts are asynchronous and synchronized internally
set_false_path -from [get_ports ext_irq_i[*]]

# ==============================================================
# 9. SLOW PERIPHERAL FALSE PATHS
# ==============================================================
# PWM fault input — async external signal
set_false_path -from [get_ports pwm_fault_i]

# Status LEDs — very slow, no timing requirement
set_false_path -to [get_ports status_led_o[*]]
set_false_path -to [get_ports cpu_halt_o]

# Watchdog reset output — asynchronous pulse
set_false_path -to [get_ports wdt_reset_o]

# ==============================================================
# 10. SPI INTERFACE
# ==============================================================
# SPI MISO is sampled asynchronously by the SPI controller
set_false_path -from [get_ports spi0_miso_i]

# ==============================================================
# 11. I2C INTERFACE
# ==============================================================
# I2C is a slow open-drain bus (100/400 kHz) — false path.
# The bidirectional pads are modelled as separate in/out after sv2v.
set_false_path -from [get_ports i2c0_sda_io]
set_false_path -to   [get_ports i2c0_sda_io]
set_false_path -from [get_ports i2c0_scl_io]
set_false_path -to   [get_ports i2c0_scl_io]

# ==============================================================
# End of CERES RISC-V SDC
# ==============================================================
