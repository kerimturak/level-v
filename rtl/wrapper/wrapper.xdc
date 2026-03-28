# =============================================================================
# Level-V — Basys3 (xc7a35tcpg236-1) pin + timing constraints
# =============================================================================
# Vivado: Bu dosyayı Constraints sources (constrs_1) içine ekleyin.
#   Implementation run → Settings → use same constraint set.
#   Dosya özellikleri: "Used in synthesis" VE "Used in implementation" AÇIK olmalı.
# Yalnızca bu 6 portlu üst modül (clk_i, rst_ni, uart0_*, prog_*) için yazıldı.
# =============================================================================

# 7-Series: 3.3 V bank ile bitstream uyarılarını azaltmak (kart 3.3 V CMOS)
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]

# Saat: 25 MHz → 40 ns (CPU_CLK ve gerçek clk_i ile aynı olmalı)
create_clock -period 40.000 -name sys_clk -add [get_ports clk_i]

# --- I/O: her porta ayrı PACKAGE_PIN + IOSTANDARD (NSTD-1 / UCIO-1 için) ---
# Basys3 referans pinleri; başka kartta pinmap'i değiştir.

set_property PACKAGE_PIN W5  [get_ports clk_i]
set_property IOSTANDARD LVCMOS33 [get_ports clk_i]

# Reset: active-low rst_ni. SW0=V17 — switch UP = run (1), DOWN = reset (0); tutmaya gerek yok.
# (U18 CPU_RESET düğmesi serbest bırakılınca sıçrar; sürekli basılı tutmak gerekirdi.)
set_property PACKAGE_PIN V17 [get_ports rst_ni]
set_property IOSTANDARD LVCMOS33 [get_ports rst_ni]

set_property PACKAGE_PIN A18 [get_ports uart0_tx_o]
set_property IOSTANDARD LVCMOS33 [get_ports uart0_tx_o]

set_property PACKAGE_PIN B18 [get_ports uart0_rx_i]
set_property IOSTANDARD LVCMOS33 [get_ports uart0_rx_i]

set_property PACKAGE_PIN J1  [get_ports prog_rx_i]
set_property IOSTANDARD LVCMOS33 [get_ports prog_rx_i]

set_property PACKAGE_PIN W18 [get_ports prog_mode_o]
set_property IOSTANDARD LVCMOS33 [get_ports prog_mode_o]

# (İsteğe bağlı) Ek gecikme: UART RX / prog RX için
# set_input_delay -clock [get_clocks sys_clk] -max 10.0 [get_ports {uart0_rx_i prog_rx_i}]
# set_input_delay -clock [get_clocks sys_clk] -min 0.0 [get_ports {uart0_rx_i prog_rx_i}]
# set_output_delay -clock [get_clocks sys_clk] -max 10.0 [get_ports uart0_tx_o]
