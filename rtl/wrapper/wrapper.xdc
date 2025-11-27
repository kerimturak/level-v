
set_property -dict { PACKAGE_PIN W5   IOSTANDARD LVCMOS33 } [get_ports { clk_i }]
create_clock -name clk_i -period 40.000 [get_ports clk_i]

set_property -dict { PACKAGE_PIN V17   IOSTANDARD LVCMOS33 } [get_ports { rst_ni }];

set_property -dict { PACKAGE_PIN U16   IOSTANDARD LVCMOS33 } [get_ports { prog_mode_led_o }];

set_property -dict { PACKAGE_PIN A18    IOSTANDARD LVCMOS33 } [get_ports { uart_tx_o }];
set_property -dict { PACKAGE_PIN B18    IOSTANDARD LVCMOS33 } [get_ports { uart_rx_i }];
set_property -dict { PACKAGE_PIN K17    IOSTANDARD LVCMOS33 } [get_ports { program_rx_i}];

