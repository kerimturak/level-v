
## Basys3 pin mappings (uncommented for this project)
# Clock: Basys3 100 MHz clock input
set_property -dict { PACKAGE_PIN W5   IOSTANDARD LVCMOS33 } [get_ports { clk_i }]
create_clock -name clk_i -period 10.000 [get_ports clk_i]

# Reset: map to center pushbutton (btnC)
set_property -dict { PACKAGE_PIN U18   IOSTANDARD LVCMOS33 } [get_ports { rst_ni }]

# Status LEDs (use user LEDs LD0..LD3)
set_property -dict { PACKAGE_PIN U16   IOSTANDARD LVCMOS33 } [get_ports { status_led_o[0] }]
set_property -dict { PACKAGE_PIN E19   IOSTANDARD LVCMOS33 } [get_ports { status_led_o[1] }]
set_property -dict { PACKAGE_PIN U19   IOSTANDARD LVCMOS33 } [get_ports { status_led_o[2] }]
set_property -dict { PACKAGE_PIN V19   IOSTANDARD LVCMOS33 } [get_ports { status_led_o[3] }]

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

