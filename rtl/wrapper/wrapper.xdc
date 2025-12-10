
## Basys3 pin mappings (uncommented for this project)
# Clock: Basys3 100 MHz clock input
set_property -dict { PACKAGE_PIN W5   IOSTANDARD LVCMOS33 } [get_ports { clk_i }]


# Reset: map to center pushbutton (btnC)
set_property -dict { PACKAGE_PIN U18   IOSTANDARD LVCMOS33 } [get_ports { rst_ni }]

# Status LEDs (use user LEDs LD0..LD3)
# set_property -dict { PACKAGE_PIN U16   IOSTANDARD LVCMOS33 } [get_ports { status_led_o[0] }]
# set_property -dict { PACKAGE_PIN E19   IOSTANDARD LVCMOS33 } [get_ports { status_led_o[1] }]
# set_property -dict { PACKAGE_PIN U19   IOSTANDARD LVCMOS33 } [get_ports { status_led_o[2] }]
# set_property -dict { PACKAGE_PIN V19   IOSTANDARD LVCMOS33 } [get_ports { status_led_o[3] }]

# Programming mode LED (map to LD4)
set_property -dict { PACKAGE_PIN W18   IOSTANDARD LVCMOS33 } [get_ports { prog_mode_o }]

# Main UART (console) -> onboard USB-RS232 (FTDI)
# Map to UART0 signals on top-level
set_property -dict { PACKAGE_PIN A18    IOSTANDARD LVCMOS33 } [get_ports { uart0_tx_o }]
set_property -dict { PACKAGE_PIN B18    IOSTANDARD LVCMOS33 } [get_ports { uart0_rx_i }]

# Programmer UART -> PMOD JA pin 1 (JA1)
# Basys3 PMOD JA mapping: JA[0] -> PACKAGE_PIN J1
set_property -dict { PACKAGE_PIN J1    IOSTANDARD LVCMOS33 } [get_ports { prog_rx_i }]

# Notes:
# - `status_led_o` is a 4-bit port (LD0..LD3). prog_mode_led_o mapped to LD4.
# - Main console UART uses on-board USB-RS232; no board changes needed for host PC connection.

## ============================================================================
## TIMING OPTIMIZATION CONSTRAINTS
## ============================================================================

# Multi-cycle paths for division unit (takes multiple cycles to complete)
# Division operations are allowed to take up to 16 cycles (for pipelined div)
# This relaxes timing constraints on division paths
set_multicycle_path -setup 16 -through [get_pins -hierarchical -filter {NAME =~ "*i_divu*"}]
set_multicycle_path -hold 15 -through [get_pins -hierarchical -filter {NAME =~ "*i_divu*"}]

# Multi-cycle paths for pipelined multiplication unit (2 cycles)
# Allow multiplier 2 cycles to complete operation
set_multicycle_path -setup 2 -through [get_pins -hierarchical -filter {NAME =~ "*i_mul_pipelined*"}]
set_multicycle_path -hold 1 -through [get_pins -hierarchical -filter {NAME =~ "*i_mul_pipelined*"}]

# Fanout optimization - replicate high-fanout nets
set_property MAX_FANOUT 20 [get_nets -hierarchical -filter {NAME =~ "*cache_req*"}]
set_property MAX_FANOUT 15 [get_nets -hierarchical -filter {NAME =~ "*fwd_*"}]

# Critical path optimization directives
# Enable retiming for better register placement
set_property KEEP_HIERARCHY SOFT [get_cells -hierarchical -filter {NAME =~ "*i_alu*"}]

# Division unit specific optimizations
set_property KEEP_HIERARCHY SOFT [get_cells -hierarchical -filter {NAME =~ "*divu*"}]

# Multiplication unit optimizations
set_property KEEP_HIERARCHY SOFT [get_cells -hierarchical -filter {NAME =~ "*mul*"}]

# Hazard unit optimization (high fanout paths)
set_property KEEP_HIERARCHY SOFT [get_cells -hierarchical -filter {NAME =~ "*i_hazard*"}]

# ============================================================================
# BRAM INFERENCE FOR WRAPPER_RAM
# ============================================================================
# Force wrapper_ram arrays to use BRAM instead of distributed RAM
# The ram0_reg through ram3_reg arrays should be implemented as Block RAM
set_property RAM_STYLE BLOCK [get_cells -hierarchical -filter {NAME =~ "*i_main_ram/ram0_reg*"}]
set_property RAM_STYLE BLOCK [get_cells -hierarchical -filter {NAME =~ "*i_main_ram/ram1_reg*"}]
set_property RAM_STYLE BLOCK [get_cells -hierarchical -filter {NAME =~ "*i_main_ram/ram2_reg*"}]
set_property RAM_STYLE BLOCK [get_cells -hierarchical -filter {NAME =~ "*i_main_ram/ram3_reg*"}]

