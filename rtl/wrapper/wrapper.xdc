# =============================================================================
# Level-V — Basys3 (xc7a35tcpg236-1) pin + timing constraints
# =============================================================================
# Vivado: Bu dosyayı Constraints sources (constrs_1) içine ekleyin.
# Üst modül: systessis_wrapper (clk_i, rst_ni, uart0_*, prog_*, GPIO, VGA, I2C).
# =============================================================================

set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]

# Ana saat: 25 MHz → 40 ns (level_param CPU_CLK ile uyumlu olmalı)
create_clock -period 40.000 -name sys_clk -add [get_ports clk_i]

# --- Saat / reset ---
set_property PACKAGE_PIN W5  [get_ports clk_i]
set_property IOSTANDARD LVCMOS33 [get_ports clk_i]

# SW0: çalıştırma için UP; reset için DOWN (active-low rst_ni)
set_property PACKAGE_PIN V17 [get_ports rst_ni]
set_property IOSTANDARD LVCMOS33 [get_ports rst_ni]

# --- UART0 (USB-UART) ---
set_property PACKAGE_PIN A18 [get_ports uart0_tx_o]
set_property IOSTANDARD LVCMOS33 [get_ports uart0_tx_o]

set_property PACKAGE_PIN B18 [get_ports uart0_rx_i]
set_property IOSTANDARD LVCMOS33 [get_ports uart0_rx_i]

# --- Programlama sırası (wrapper_ram) ---
set_property PACKAGE_PIN J1  [get_ports prog_rx_i]
set_property IOSTANDARD LVCMOS33 [get_ports prog_rx_i]

# prog modu göstergesi — kart üzeri LED4 (W18)
set_property PACKAGE_PIN W18 [get_ports prog_mode_o]
set_property IOSTANDARD LVCMOS33 [get_ports prog_mode_o]

# --- GPIO: SW15..SW1 → gpio_sw_i[14:0]; SW0 = rst (üstte) ---
# Digilent isimlendirmesi: sw[k] ; burada gpio_sw_i[k-1] = sw[k].
set_property PACKAGE_PIN V16 [get_ports {gpio_sw_i[0]}]
set_property PACKAGE_PIN W16 [get_ports {gpio_sw_i[1]}]
set_property PACKAGE_PIN W17 [get_ports {gpio_sw_i[2]}]
set_property PACKAGE_PIN W15 [get_ports {gpio_sw_i[3]}]
set_property PACKAGE_PIN V15 [get_ports {gpio_sw_i[4]}]
set_property PACKAGE_PIN W14 [get_ports {gpio_sw_i[5]}]
set_property PACKAGE_PIN W13 [get_ports {gpio_sw_i[6]}]
set_property PACKAGE_PIN V2  [get_ports {gpio_sw_i[7]}]
set_property PACKAGE_PIN T3  [get_ports {gpio_sw_i[8]}]
set_property PACKAGE_PIN T2  [get_ports {gpio_sw_i[9]}]
set_property PACKAGE_PIN R3  [get_ports {gpio_sw_i[10]}]
set_property PACKAGE_PIN W2  [get_ports {gpio_sw_i[11]}]
set_property PACKAGE_PIN U1  [get_ports {gpio_sw_i[12]}]
set_property PACKAGE_PIN T1  [get_ports {gpio_sw_i[13]}]
set_property PACKAGE_PIN R2  [get_ports {gpio_sw_i[14]}]
set_property IOSTANDARD LVCMOS33 [get_ports {gpio_sw_i[*]}]

# --- GPIO çıkışları: LED[15:0] (gpio_led_o[4] mantıksal olarak düşük; fiziksel LED4 = prog_mode) ---
set_property PACKAGE_PIN U16 [get_ports {gpio_led_o[0]}]
set_property PACKAGE_PIN E19 [get_ports {gpio_led_o[1]}]
set_property PACKAGE_PIN U19 [get_ports {gpio_led_o[2]}]
set_property PACKAGE_PIN V19 [get_ports {gpio_led_o[3]}]
set_property PACKAGE_PIN U15 [get_ports {gpio_led_o[5]}]
set_property PACKAGE_PIN U14 [get_ports {gpio_led_o[6]}]
set_property PACKAGE_PIN V14 [get_ports {gpio_led_o[7]}]
set_property PACKAGE_PIN V13 [get_ports {gpio_led_o[8]}]
set_property PACKAGE_PIN V3  [get_ports {gpio_led_o[9]}]
set_property PACKAGE_PIN W3  [get_ports {gpio_led_o[10]}]
set_property PACKAGE_PIN U3  [get_ports {gpio_led_o[11]}]
set_property PACKAGE_PIN P3  [get_ports {gpio_led_o[12]}]
set_property PACKAGE_PIN N3  [get_ports {gpio_led_o[13]}]
set_property PACKAGE_PIN P1  [get_ports {gpio_led_o[14]}]
set_property PACKAGE_PIN L1  [get_ports {gpio_led_o[15]}]
# gpio_led_o[4] sürekli 0 (prog_mode_o LED4/W18’i kullanıyor); fiziksel pin JB1
set_property PACKAGE_PIN A14 [get_ports {gpio_led_o[4]}]
set_property IOSTANDARD LVCMOS33 [get_ports {gpio_led_o[*]}]

# gpio_o[4] — prog_mode ile aynı LEDe gitmediği için Pmod JA3 (sch JA[2])
set_property PACKAGE_PIN J2  [get_ports gpio_led4_aux_o]
set_property IOSTANDARD LVCMOS33 [get_ports gpio_led4_aux_o]

# --- Kart VGA konnektörü (12-bit RGB + Hsync/Vsync) ---
set_property PACKAGE_PIN G19 [get_ports {vga_r_o[0]}]
set_property PACKAGE_PIN H19 [get_ports {vga_r_o[1]}]
set_property PACKAGE_PIN J19 [get_ports {vga_r_o[2]}]
set_property PACKAGE_PIN N19 [get_ports {vga_r_o[3]}]
set_property PACKAGE_PIN J17 [get_ports {vga_g_o[0]}]
set_property PACKAGE_PIN H17 [get_ports {vga_g_o[1]}]
set_property PACKAGE_PIN G17 [get_ports {vga_g_o[2]}]
set_property PACKAGE_PIN D17 [get_ports {vga_g_o[3]}]
set_property PACKAGE_PIN N18 [get_ports {vga_b_o[0]}]
set_property PACKAGE_PIN L18 [get_ports {vga_b_o[1]}]
set_property PACKAGE_PIN K18 [get_ports {vga_b_o[2]}]
set_property PACKAGE_PIN J18 [get_ports {vga_b_o[3]}]
set_property PACKAGE_PIN P19 [get_ports vga_hsync_o]
set_property PACKAGE_PIN R19 [get_ports vga_vsync_o]
set_property IOSTANDARD LVCMOS33 [get_ports {vga_r_o[*]}]
set_property IOSTANDARD LVCMOS33 [get_ports {vga_g_o[*]}]
set_property IOSTANDARD LVCMOS33 [get_ports {vga_b_o[*]}]
set_property IOSTANDARD LVCMOS33 [get_ports vga_hsync_o]
set_property IOSTANDARD LVCMOS33 [get_ports vga_vsync_o]

# --- I2C: Pmod JC[1:0]; harici pull-up gerekir (kartta yoksa RC’ye PULLUP ekleyin) ---
set_property PACKAGE_PIN K17 [get_ports i2c0_sda_io]
set_property PACKAGE_PIN M18 [get_ports i2c0_scl_io]
set_property IOSTANDARD LVCMOS33 [get_ports i2c0_sda_io]
set_property IOSTANDARD LVCMOS33 [get_ports i2c0_scl_io]
set_property PULLUP true [get_ports i2c0_sda_io]
set_property PULLUP true [get_ports i2c0_scl_io]
