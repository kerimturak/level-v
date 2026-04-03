# =============================================================================
# Level-V — Nexys A7-100T (xc7a100tcsg324-1) pin + timing constraints
# =============================================================================
# Vivado: Bu dosyayı Constraints sources (constrs_1) içine ekleyin.
# Üst modül: systessis_wrapper (clk_i, rst_ni, uart0_*, prog_*, GPIO, VGA, I2C).
# Kaynak: Digilent Nexys A7-100T Reference Manual & Master XDC
# =============================================================================

set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]

# =============================================================================
# Saat ve Reset
# =============================================================================
# Kart osilatörü: 100 MHz → clk_wiz_0 ile CPU_CLK'a (25 MHz) dönüşüm yapılır.
# create_clock fiziksel osilatör frekansını tanımlar; clk_wiz çıkışı Vivado
# tarafından otomatik türetilir.
create_clock -period 10.000 -name sys_clk -add [get_ports clk_i]

set_property PACKAGE_PIN E3  [get_ports clk_i]
set_property IOSTANDARD LVCMOS33 [get_ports clk_i]

# CPU_RESETN butonu (active-low — tasarımla doğrudan uyumlu)
set_property PACKAGE_PIN C12 [get_ports rst_ni]
set_property IOSTANDARD LVCMOS33 [get_ports rst_ni]

# =============================================================================
# UART0 (USB-UART köprüsü — Microchip MCP2221A / FTDI)
# =============================================================================
# UART_RXD_OUT: FPGA TX → USB bridge RX → PC
set_property PACKAGE_PIN D4  [get_ports uart0_tx_o]
set_property IOSTANDARD LVCMOS33 [get_ports uart0_tx_o]

# UART_TXD_IN: PC → USB bridge TX → FPGA RX
set_property PACKAGE_PIN C4  [get_ports uart0_rx_i]
set_property IOSTANDARD LVCMOS33 [get_ports uart0_rx_i]

# =============================================================================
# Programlama kanalı (wrapper_ram UART yükleyici)
# =============================================================================
# Pmod JD[1] — harici USB-UART modülü bağlanır
set_property PACKAGE_PIN H4  [get_ports prog_rx_i]
set_property IOSTANDARD LVCMOS33 [get_ports prog_rx_i]

# prog_mode göstergesi — Pmod JD[2]
set_property PACKAGE_PIN H1  [get_ports prog_mode_o]
set_property IOSTANDARD LVCMOS33 [get_ports prog_mode_o]

# =============================================================================
# GPIO Girişler: SW[14:0] → gpio_sw_i[14:0]
# =============================================================================
# Nexys A7'de ayrı CPU_RESETN butonu var; tüm switch'ler kullanılabilir.
set_property PACKAGE_PIN J15 [get_ports {gpio_sw_i[0]}]
set_property PACKAGE_PIN L16 [get_ports {gpio_sw_i[1]}]
set_property PACKAGE_PIN M13 [get_ports {gpio_sw_i[2]}]
set_property PACKAGE_PIN R15 [get_ports {gpio_sw_i[3]}]
set_property PACKAGE_PIN R17 [get_ports {gpio_sw_i[4]}]
set_property PACKAGE_PIN T18 [get_ports {gpio_sw_i[5]}]
set_property PACKAGE_PIN U18 [get_ports {gpio_sw_i[6]}]
set_property PACKAGE_PIN R13 [get_ports {gpio_sw_i[7]}]
set_property PACKAGE_PIN T8  [get_ports {gpio_sw_i[8]}]
set_property PACKAGE_PIN U8  [get_ports {gpio_sw_i[9]}]
set_property PACKAGE_PIN R16 [get_ports {gpio_sw_i[10]}]
set_property PACKAGE_PIN T13 [get_ports {gpio_sw_i[11]}]
set_property PACKAGE_PIN H6  [get_ports {gpio_sw_i[12]}]
set_property PACKAGE_PIN U12 [get_ports {gpio_sw_i[13]}]
set_property PACKAGE_PIN U11 [get_ports {gpio_sw_i[14]}]
set_property IOSTANDARD LVCMOS33 [get_ports {gpio_sw_i[*]}]

# =============================================================================
# GPIO Çıkışlar: LED[15:0] → gpio_led_o[15:0]
# =============================================================================
# Not: gpio_led_o[4] systessis_wrapper'da 1'b0'a bağlı (gpio_o[4] → gpio_led4_aux_o).
set_property PACKAGE_PIN H17 [get_ports {gpio_led_o[0]}]
set_property PACKAGE_PIN K15 [get_ports {gpio_led_o[1]}]
set_property PACKAGE_PIN J13 [get_ports {gpio_led_o[2]}]
set_property PACKAGE_PIN N14 [get_ports {gpio_led_o[3]}]
set_property PACKAGE_PIN R18 [get_ports {gpio_led_o[4]}]
set_property PACKAGE_PIN V17 [get_ports {gpio_led_o[5]}]
set_property PACKAGE_PIN U17 [get_ports {gpio_led_o[6]}]
set_property PACKAGE_PIN U16 [get_ports {gpio_led_o[7]}]
set_property PACKAGE_PIN V16 [get_ports {gpio_led_o[8]}]
set_property PACKAGE_PIN T15 [get_ports {gpio_led_o[9]}]
set_property PACKAGE_PIN U14 [get_ports {gpio_led_o[10]}]
set_property PACKAGE_PIN T16 [get_ports {gpio_led_o[11]}]
set_property PACKAGE_PIN V15 [get_ports {gpio_led_o[12]}]
set_property PACKAGE_PIN V14 [get_ports {gpio_led_o[13]}]
set_property PACKAGE_PIN V12 [get_ports {gpio_led_o[14]}]
set_property PACKAGE_PIN V11 [get_ports {gpio_led_o[15]}]
set_property IOSTANDARD LVCMOS33 [get_ports {gpio_led_o[*]}]

# gpio_o[4] yardımcı çıkış — Pmod JD[3]
set_property PACKAGE_PIN G1  [get_ports gpio_led4_aux_o]
set_property IOSTANDARD LVCMOS33 [get_ports gpio_led4_aux_o]

# =============================================================================
# VGA konnektörü (12-bit RGB + Hsync/Vsync)
# =============================================================================
set_property PACKAGE_PIN A3  [get_ports {vga_r_o[0]}]
set_property PACKAGE_PIN B4  [get_ports {vga_r_o[1]}]
set_property PACKAGE_PIN C5  [get_ports {vga_r_o[2]}]
set_property PACKAGE_PIN A4  [get_ports {vga_r_o[3]}]

set_property PACKAGE_PIN C6  [get_ports {vga_g_o[0]}]
set_property PACKAGE_PIN A5  [get_ports {vga_g_o[1]}]
set_property PACKAGE_PIN B6  [get_ports {vga_g_o[2]}]
set_property PACKAGE_PIN A6  [get_ports {vga_g_o[3]}]

set_property PACKAGE_PIN B7  [get_ports {vga_b_o[0]}]
set_property PACKAGE_PIN C7  [get_ports {vga_b_o[1]}]
set_property PACKAGE_PIN D7  [get_ports {vga_b_o[2]}]
set_property PACKAGE_PIN D8  [get_ports {vga_b_o[3]}]

set_property PACKAGE_PIN B11 [get_ports vga_hsync_o]
set_property PACKAGE_PIN B12 [get_ports vga_vsync_o]

set_property IOSTANDARD LVCMOS33 [get_ports {vga_r_o[*]}]
set_property IOSTANDARD LVCMOS33 [get_ports {vga_g_o[*]}]
set_property IOSTANDARD LVCMOS33 [get_ports {vga_b_o[*]}]
set_property IOSTANDARD LVCMOS33 [get_ports vga_hsync_o]
set_property IOSTANDARD LVCMOS33 [get_ports vga_vsync_o]

# =============================================================================
# I2C — Pmod JC[1:2]; harici pull-up gereklidir (yoksa PULLUP kullanılır)
# =============================================================================
set_property PACKAGE_PIN K1  [get_ports i2c0_sda_io]
set_property PACKAGE_PIN F6  [get_ports i2c0_scl_io]
set_property IOSTANDARD LVCMOS33 [get_ports i2c0_sda_io]
set_property IOSTANDARD LVCMOS33 [get_ports i2c0_scl_io]
set_property PULLUP true [get_ports i2c0_sda_io]
set_property PULLUP true [get_ports i2c0_scl_io]

# =============================================================================
# Zamanlama kısıtları
# =============================================================================
# clk_wiz çıkış saati Vivado tarafından otomatik türetilir (derived clock).
# Eğer clk_wiz kullanılmıyorsa (doğrudan 100 MHz), aşağıdaki satırı açın:
# create_generated_clock -name cpu_clk -source [get_ports clk_i] -divide_by 4 \
#   [get_pins clk_generator/clk_out1]

# Giriş/çıkış gecikmeleri — UART, GPIO, VGA asenkron; gevşek kısıtlar yeterli.
set_input_delay  -clock sys_clk -max 5.0 [get_ports uart0_rx_i]
set_input_delay  -clock sys_clk -min 0.0 [get_ports uart0_rx_i]
set_output_delay -clock sys_clk -max 5.0 [get_ports uart0_tx_o]
set_output_delay -clock sys_clk -min 0.0 [get_ports uart0_tx_o]

set_input_delay  -clock sys_clk -max 5.0 [get_ports prog_rx_i]
set_input_delay  -clock sys_clk -min 0.0 [get_ports prog_rx_i]

# GPIO ve VGA asenkron; false path olarak işaretle
set_false_path -from [get_ports {gpio_sw_i[*]}]
set_false_path -from [get_ports rst_ni]
set_false_path -to   [get_ports {gpio_led_o[*]}]
set_false_path -to   [get_ports gpio_led4_aux_o]
set_false_path -to   [get_ports prog_mode_o]
set_false_path -to   [get_ports {vga_r_o[*]}]
set_false_path -to   [get_ports {vga_g_o[*]}]
set_false_path -to   [get_ports {vga_b_o[*]}]
set_false_path -to   [get_ports vga_hsync_o]
set_false_path -to   [get_ports vga_vsync_o]

# I2C yavaş protokol — false path
set_false_path -to   [get_ports i2c0_sda_io]
set_false_path -to   [get_ports i2c0_scl_io]
set_false_path -from [get_ports i2c0_sda_io]
set_false_path -from [get_ports i2c0_scl_io]

# =============================================================================
# Bitstream Seçenekleri
# =============================================================================
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 33 [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]
