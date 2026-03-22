onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -group WRAPPER -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_reg_file/registers
add wave -noupdate -group WRAPPER -group uart_tx_fifo -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/i_tx_buffer/DATA_WIDTH
add wave -noupdate -group WRAPPER -group uart_tx_fifo -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/i_tx_buffer/FIFO_DEPTH
add wave -noupdate -group WRAPPER -group uart_tx_fifo -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/i_tx_buffer/ADDR_WIDTH
add wave -noupdate -group WRAPPER -group uart_tx_fifo -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/i_tx_buffer/clk
add wave -noupdate -group WRAPPER -group uart_tx_fifo -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/i_tx_buffer/rst
add wave -noupdate -group WRAPPER -group uart_tx_fifo -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/i_tx_buffer/write_en
add wave -noupdate -group WRAPPER -group uart_tx_fifo -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/i_tx_buffer/read_en
add wave -noupdate -group WRAPPER -group uart_tx_fifo -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/i_tx_buffer/write_data
add wave -noupdate -group WRAPPER -group uart_tx_fifo -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/i_tx_buffer/read_data
add wave -noupdate -group WRAPPER -group uart_tx_fifo -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/i_tx_buffer/full
add wave -noupdate -group WRAPPER -group uart_tx_fifo -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/i_tx_buffer/empty
add wave -noupdate -group WRAPPER -group uart_tx_fifo -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/i_tx_buffer/fifo_mem
add wave -noupdate -group WRAPPER -group uart_tx_fifo -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/i_tx_buffer/write_ptr
add wave -noupdate -group WRAPPER -group uart_tx_fifo -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/i_tx_buffer/read_ptr
add wave -noupdate -group WRAPPER -group uart_tx_fifo -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/i_tx_buffer/wrap_around
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MVENDORID
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MARCHID
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MIMPID
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MHARTID
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MCONFIGPTR
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MSTATUS
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MISA
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MIE_ADDR
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MTVEC
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MCOUNTEREN
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MSTATUSH
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MSCRATCH
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MEPC
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MCAUSE
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MTVAL
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MIP
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MCYCLE
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MINSTRET
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MCYCLEH
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MINSTRETH
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/CYCLE
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/INSTRET
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/CYCLEH
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/INSTRETH
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/SCOUNTEREN
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MCOUNTINHIBIT
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/PMPCFG0
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/PMPADDR0
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/TSELECT
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/TDATA1
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/TDATA2
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/TDATA3
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/TCONTROL
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/LEVEL_MISA
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MISA_WRITABLE_MASK
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MIE_RW_MASK
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MIP_RW_MASK
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/clk_i
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/rst_ni
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/stall_i
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/rd_en_i
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/wr_en_i
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/csr_idx_i
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/csr_wdata_i
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/csr_rdata_o
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/trap_active_i
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/de_trap_active_i
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/instr_type_i
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/trap_cause_i
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/trap_mepc_i
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/trap_tval_i
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/pc_i
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/timer_irq_i
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/sw_irq_i
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/ext_irq_i
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mtvec_o
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mepc_o
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/misa_c_o
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/csr_write_valid_o
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tdata1_o
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tdata2_o
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tcontrol_o
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mstatus
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/misa
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mie
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mtvec
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mip
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mscratch
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mepc
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mcause
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mtval_reg
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mcycle
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mcycleh
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/minstret
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/minstreth
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/pmpcfg0
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/pmpaddr0
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tselect_reg
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tcontrol_reg
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tdata1_reg
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tdata2_reg
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tcontrol_out_reg
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tdata1_bypass
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tdata2_bypass
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tcontrol_bypass
add wave -noupdate -group WRAPPER -group CSR -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tselect_safe
add wave -noupdate -group WRAPPER -group in -radix hexadecimal /tb_wrapper/level_wrapper/clk_i
add wave -noupdate -group WRAPPER -group in -radix hexadecimal /tb_wrapper/level_wrapper/rst_ni
add wave -noupdate -group WRAPPER -group in -radix hexadecimal /tb_wrapper/level_wrapper/uart0_rx_i
add wave -noupdate -group WRAPPER -group in -radix hexadecimal /tb_wrapper/level_wrapper/uart1_rx_i
add wave -noupdate -group WRAPPER -group in -radix hexadecimal /tb_wrapper/level_wrapper/spi0_miso_i
add wave -noupdate -group WRAPPER -group in -radix hexadecimal /tb_wrapper/level_wrapper/gpio_i
add wave -noupdate -group WRAPPER -group in -radix hexadecimal /tb_wrapper/level_wrapper/pwm_fault_i
add wave -noupdate -group WRAPPER -group in -radix hexadecimal /tb_wrapper/level_wrapper/ext_irq_i
add wave -noupdate -group WRAPPER -group in -radix hexadecimal /tb_wrapper/level_wrapper/prog_rx_i
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/uart0_tx_o
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/uart1_tx_o
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/spi0_sclk_o
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/spi0_mosi_o
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/spi0_ss_o
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/gpio_o
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/gpio_oe_o
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/pwm_o
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/pwm_n_o
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/wdt_reset_o
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/vga_hsync_o
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/vga_vsync_o
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/vga_r_o
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/vga_g_o
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/vga_b_o
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/prog_mode_o
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/cpu_halt_o
add wave -noupdate -group WRAPPER -group out -radix hexadecimal /tb_wrapper/level_wrapper/status_led_o
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/CLK_FREQ_HZ
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/BAUD_RATE
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/RAM_SIZE_KB
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/RAM_LATENCY
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/BOOTROM_EN
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/BOOTROM_SIZE_KB
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/NUM_UART
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/SPI_EN
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/I2C_EN
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/GPIO_EN
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/PWM_EN
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/TIMER_EN
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/PLIC_EN
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/WDT_EN
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/DMA_EN
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/VGA_EN
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/DEBUG_EN
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/JTAG_EN
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/PROG_SEQUENCE
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/RAM_DEPTH
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/CACHE_LINE_W
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/BYTE_OFFSET
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/SLV_RAM
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/SLV_CLINT
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/SLV_PBUS
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/WB_NUM_SLAVES_LOCAL
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/cpu_mem_req
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/cpu_mem_res
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/wb_cpu_m
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/wb_cpu_s
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/wb_slave_m
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/wb_slave_s
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/prog_reset
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/sys_rst_n
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_rdata
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_wstrb
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_rd_en
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_addr
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_delay_q
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_pending_q
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_wb_req
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_wb_we
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_wb_addr
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_wb_wdata
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_wb_sel
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_wb_rdata
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_wb_ack
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_burst_active
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_burst_cnt
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_burst_base_addr
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_burst_data_q
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_burst_data_valid
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/timer_irq
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/sw_irq
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/pbus_addr
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/pbus_wdata
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/pbus_wstrb
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/pbus_valid
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/pbus_we
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/pbus_rdata
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/pbus_ready
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/sel_ram
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/sel_clint
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/sel_periph
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/sel_uart0
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/sel_uart1
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/sel_spi0
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/sel_i2c0
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/sel_gpio
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/sel_pwm
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/sel_timer
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/sel_plic
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/sel_wdt
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/sel_dma
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/sel_vga
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/uart0_rdata
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/uart1_rdata
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/spi0_rdata
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i2c0_rdata
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i2c0_scl_o
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i2c0_scl_oe
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i2c0_scl_i
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i2c0_sda_o
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i2c0_sda_oe
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i2c0_sda_i
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i2c0_irq
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/gpio_rdata
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/gpio_irq
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/pwm_rdata
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/pwm_out
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/pwm_n_out
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/pwm_irq
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/pwm_sync
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/timer_rdata
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/timer_pwm
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/gptimer_irq
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/gptimer_irq_combined
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/plic_rdata
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/plic_irq_sources
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/plic_irq
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/wdt_rdata
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/wdt_irq
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/wdt_reset
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/dma_rdata
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/dma_irq
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/dma_req
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/dma_addr
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/dma_wdata
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/dma_wstrb
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/dma_ack
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/vga_rdata
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/pixel_clk
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/pll_locked
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_res
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/clint_res
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/periph_res
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/uart_sel
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/spi_sel
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i2c_sel
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i2c_scl_i
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i2c_sda_i
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i2c_irq
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_is_burst
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_is_burst_start
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_is_burst_end
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_wdata_expanded
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_wstrb_expanded
add wave -noupdate -group WRAPPER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/ram_word_offset
add wave -noupdate -group WRAPPER -group SOC -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/clk_i
add wave -noupdate -group WRAPPER -group SOC -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/timer_irq_i
add wave -noupdate -group WRAPPER -group SOC -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/sw_irq_i
add wave -noupdate -group WRAPPER -group SOC -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ext_irq_i
add wave -noupdate -group WRAPPER -group SOC -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/iomem_res_i
add wave -noupdate -group WRAPPER -group SOC -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/iomem_req_o
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/stall_cause
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/lx_ireq
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/lx_dres
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/lx_dreq
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/fe_stall
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/fe_lx_ires
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/fe_imiss_stall
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/fe_pc
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/fe_pc_incr
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/fe_inst
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/fe_spec
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/fe_exc_type
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/fe_active_exc_type
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/fe_instr_type
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/fencei_flush
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/flush_pc
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/fe_tracer
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/fe_trap_active
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/pipe1
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/de_ctrl
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/de_enable
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/de_stall
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/de_flush
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/de_flush_en
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/de_r1_data
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/de_r2_data
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/de_fwd_a
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/de_fwd_b
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/de_imm
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/de_exc_type
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/de_info
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/de_active_exc_type
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/pipe2
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_flush
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_flush_en
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_fwd_a
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_fwd_b
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_alu_result
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_pc_target
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_pc_target_last
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_wdata
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_pc_sel
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_alu_stall
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_spec_hit
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_exc_type
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_alu_exc_type
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_rd_csr
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_wr_csr
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_mtvec
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_misa_c
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_tdata1
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_tdata2
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_tcontrol
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_info
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_valid_csr
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_trap_cause
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_trap_mepc
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_csr_write_valid
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_csr_wr_data
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_data_req
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/de_trap_active
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/pipe3
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/me_dmiss_stall
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/me_fencei_stall
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/me_rdata
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/me_data_req
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/pipe4
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/wb_rf_rw
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/wb_data
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/excp_mask
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/priority_flush
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/trap_active
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/trap_tval
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/arb_iomem_req
add wave -noupdate -group WRAPPER -group SOC -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/arb_iomem_res
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/RESET_VECTOR
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/IC_NUM_SET
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/DC_NUM_SET
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/MAX_FLUSH_CYCLES
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/FLUSH_CNT_WIDTH
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/fe_tracer_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/clk_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/stall_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/flush_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/flush_pc_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/lx_ires_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/pc_target_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/ex_mtvec_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/trap_active_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/misa_c_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/tdata1_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/tdata2_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/tcontrol_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/spec_hit_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/spec_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/lx_ireq_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/pc_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/pc_incr_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/inst_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/imiss_stall_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/exc_type_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/de_info_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/ex_info_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/instr_type_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/pc
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/pc_next
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/pc_en
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/fetch_valid
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/fetch_valid_reg
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/uncached
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/uncached_next
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/memregion
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/memregion_next
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/grand
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/grand_next
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/illegal_instr
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/is_comp
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/buff_res
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/buff_req
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/icache_res
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/abuff_icache_req
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/icache_req
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/buff_lowX_res
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/buf_lookup_ack
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/flush_counter
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/flush_in_progress
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/has_debug_breakpoint
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/has_instr_misaligned
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/has_instr_access_fault
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/has_illegal_instr
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/has_ebreak
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/has_ecall
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/trigger0_execute_hit
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/trigger1_execute_hit
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/prev_icache_req_valid
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/CACHE_SIZE
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/BLK_SIZE
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/XLEN
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/NUM_WAY
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/NUM_SET
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/IDX_WIDTH
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/BOFFSET
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/WOFFSET
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/TAG_SIZE
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/flush
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/flush_index
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/cache_req_q
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/rd_idx
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/wr_idx
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/cache_idx
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/cache_miss
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/cache_hit
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/updated_node
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/cache_valid_vec
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/cache_hit_vec
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/evict_way
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/cache_select_data
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/cache_wr_way
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/cache_wr_en
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/lookup_ack
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/dsram
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/tsram
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/nsram
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/node_q
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/clk_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/spec_hit_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/stall_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/inst_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/pc_target_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/pc_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/pc_incr_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/fetch_valid_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/spec_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/de_info_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/ex_info_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/ghr
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/ghr_spec
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/ghr_recover
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/pht
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/bimodal
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/choice
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/btb_valid
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/btb_tag
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/btb_target
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/ibtc_valid
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/ibtc_tag
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/ibtc_target
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/loop_idx
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/loop_count
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/loop_trip
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/loop_valid
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/loop_tag
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/imm
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/j_type
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/jr_type
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/b_type
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/req_valid
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/return_addr
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/restore
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/popped
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/pht_rd_idx
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/pht_wr_idx
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/bimodal_rd_idx
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/bimodal_wr_idx
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/btb_rd_idx
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/btb_wr_idx
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/ibtc_rd_idx
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/ibtc_wr_idx
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/btb_hit
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/btb_predicted_target
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/ibtc_hit
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/ibtc_predicted_target
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/pht_taken
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/bimodal_taken
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/use_gshare
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/final_taken
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/loop_hit
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/loop_pred_exit
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/loop_current_count
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/spec_miss
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/ex_is_branch
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/ex_was_taken
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/is_backward_branch
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/branch_target_calc
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/high_confidence
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group RAS -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/i_ras/RAS_SIZE
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group RAS -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/i_ras/clk_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group RAS -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/i_ras/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group RAS -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/i_ras/restore_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group RAS -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/i_ras/req_valid_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group RAS -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/i_ras/j_type_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group RAS -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/i_ras/jr_type_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group RAS -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/i_ras/rd_addr_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group RAS -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/i_ras/r1_addr_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group RAS -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/i_ras/return_addr_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group RAS -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/i_ras/popped_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group RAS -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/i_ras/ras
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group RAS -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/i_ras/ras_op
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group RAS -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/i_ras/link_rd
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group BP -group RAS -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_gshare_bp/i_ras/link_r1
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group IPMA -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_pma/NUM_REGIONS
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group IPMA -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_pma/pma_map
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group IPMA -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_pma/addr_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group IPMA -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_pma/uncached_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group IPMA -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_pma/memregion_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group IPMA -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_pma/grand_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group IPMA -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_pma/region_match
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/clk_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/flush_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/buff_req_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/lowX_res_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/buff_res_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/lowX_req_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/CACHE_SIZE
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/BLK_SIZE
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/XLEN
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/NUM_WAY
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/NUM_SET
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/IDX_WIDTH
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/OFFSET_WIDTH
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/TAG_SIZE
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/WORD_BITS
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/NUM_WORDS
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/WORD_SEL_WIDTH
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/PARCEL_BITS
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/PARCELS_PER_WORD
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/NUM_PARCELS
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/BLOCK_BYTES
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/even
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/odd
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/miss_state
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/hit_state
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/wr_idx
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/tag_wr_en
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/data_wr_en
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/wr_tag
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/ebram
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/obram
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/tag_ram
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/word_sel
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/half_sel
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/overflow
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/unalign
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/tag_plus1
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/masked_valid
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/ignore_valid_q
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/waiting_second_q
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/even_parcel_sel
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/odd_parcel_sel
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/even_deviceX_sel
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/odd_deviceX_sel
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {ALIGN BUFFER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_align_buffer/parcel_idx
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/clk_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/flush_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/cache_req_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/lowX_res_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/cache_res_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_icache/lowX_req_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/instr_i
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/instr_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/is_compressed_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/illegal_instr_o
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/OPCODE_LOAD
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/OPCODE_STORE
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/OPCODE_BRANCH
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/OPCODE_JALR
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/OPCODE_JAL
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/OPCODE_OPIMM
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/OPCODE_OP
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/OPCODE_LUI
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/OPCODE_SYSTEM
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/FUNCT3_ADD
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/FUNCT3_SLL
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/FUNCT3_LW
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/FUNCT3_SW
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/FUNCT3_XOR
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/FUNCT3_SRL
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/FUNCT3_OR
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/FUNCT3_AND
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/FUNCT3_BEQ
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/FUNCT3_BNE
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/FUNCT7_ZERO
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/FUNCT7_SUB
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/REG_ZERO
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/REG_RA
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/REG_SP
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/quadrant
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/funct3
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/rd_rs1_full
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/rs2_full
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/rd_prime
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/rs1_prime
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/rs2_prime
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/c0_instr
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/c1_instr
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/c2_instr
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/c0_illegal
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/c1_illegal
add wave -noupdate -group WRAPPER -group SOC -group FETCH1 -group {COMP DECODER} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/i_compressed_decoder/c2_illegal
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/clk_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/inst_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/fwd_a_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/fwd_b_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/wb_data_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/rd_addr_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/rf_rw_en_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/instr_type_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/r1_data_o
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/r2_data_o
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/ctrl_o
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/imm_o
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/exc_type_o
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/r1_data
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/r2_data
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {CONTROL UNIT} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_control_unit/inst_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {CONTROL UNIT} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_control_unit/instr_type_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {CONTROL UNIT} -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_control_unit/ctrl_o
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {CONTROL UNIT} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_control_unit/illegal_shift
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {CONTROL UNIT} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_control_unit/csr_supported
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {CONTROL UNIT} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_control_unit/csr_write_intent
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {CONTROL UNIT} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_control_unit/instr_is_csr
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {CONTROL UNIT} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_control_unit/csr_read_only
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {REG FILE} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_reg_file/clk_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {REG FILE} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_reg_file/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {REG FILE} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_reg_file/rw_en_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {REG FILE} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_reg_file/r1_addr_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {REG FILE} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_reg_file/r2_addr_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {REG FILE} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_reg_file/waddr_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {REG FILE} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_reg_file/wdata_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {REG FILE} -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_reg_file/r1_data_o
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {REG FILE} -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_reg_file/r2_data_o
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group {REG FILE} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_reg_file/registers
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group EXTEND -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_extend/imm_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group EXTEND -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_extend/sel_i
add wave -noupdate -group WRAPPER -group SOC -group DECODE2 -group EXTEND -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_extend/imm_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/csr_wr_data_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/csr_write_valid_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/clk_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/stall_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/fwd_a_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/fwd_b_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/alu_result_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/wb_data_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/r1_data_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/r2_data_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/alu_in1_sel_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/alu_in2_sel_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/rd_csr_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/wr_csr_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/csr_idx_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/csr_or_data_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/trap_active_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/de_trap_active_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/trap_cause_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/trap_tval_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/trap_mepc_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/timer_irq_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/sw_irq_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/ext_irq_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/pc_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/pc_incr_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/imm_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/pc_sel_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/alu_ctrl_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/instr_type_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/misa_c_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/write_data_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/pc_target_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/alu_result_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/pc_sel_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/alu_stall_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/exc_type_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/mtvec_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/misa_c_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/tdata1_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/tdata2_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/tcontrol_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/data_a
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/operant_a
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/operant_b
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/signed_imm
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/ex_zero
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/ex_slt
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/ex_sltu
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/tdata1
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/tdata2
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/tcontrol
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/alu_result
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/csr_rdata
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/mepc
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/misa_c
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/tcontrol_effective
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/tdata1_effective
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/tdata2_effective
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/trigger0_hit
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/trigger1_hit
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/target_misaligned
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/rd_data
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/clk_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/csr_rdata_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/alu_a_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/alu_b_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/op_sel_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/alu_stall_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/zero_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/slt_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/sltu_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/alu_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/rslt
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/abs_A
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/abs_B
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/mul_type
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/div_type
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/mul_sign
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/div_sign_quot
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/div_sign_rem
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/mul_start
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/div_start
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/mul_op_A
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/mul_op_B
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/div_op_A
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/div_op_B
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/product
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/quotient
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/remainder
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/mul_stall
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/div_stall
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/alu_stall_q
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/mul_busy
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/div_busy
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/mul_valid
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/div_valid
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/unsigned_prod
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/unsigned_quo
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/unsigned_rem
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/mul_done
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/div_done
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/div_dbz
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/div_quot_final
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group ALU -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_alu/div_rem_final
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/clk_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/stall_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/rd_en_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/wr_en_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/csr_idx_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/csr_wdata_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/trap_active_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/de_trap_active_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/instr_type_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/trap_cause_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/trap_mepc_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/trap_tval_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/pc_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/timer_irq_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/sw_irq_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/ext_irq_i
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/csr_rdata_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mtvec_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mepc_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/misa_c_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/csr_write_valid_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tdata1_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tdata2_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tcontrol_o
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MVENDORID
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MARCHID
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MIMPID
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MHARTID
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MCONFIGPTR
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MSTATUS
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MISA
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MIE_ADDR
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MTVEC
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MCOUNTEREN
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MSTATUSH
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MSCRATCH
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MEPC
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MCAUSE
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MTVAL
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MIP
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MCYCLE
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MINSTRET
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MCYCLEH
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MINSTRETH
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/CYCLE
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/INSTRET
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/CYCLEH
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/INSTRETH
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/SCOUNTEREN
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MCOUNTINHIBIT
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/PMPCFG0
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/PMPADDR0
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/TSELECT
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/TDATA1
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/TDATA2
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/TDATA3
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/TCONTROL
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/LEVEL_MISA
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MISA_WRITABLE_MASK
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MIE_RW_MASK
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/MIP_RW_MASK
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mstatus
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/misa
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mie
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mtvec
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mip
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mscratch
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mepc
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mcause
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mtval_reg
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mcycle
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/mcycleh
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/minstret
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/minstreth
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/pmpcfg0
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/pmpaddr0
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tselect_reg
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tcontrol_reg
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tdata1_reg
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tdata2_reg
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tcontrol_out_reg
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tdata1_bypass
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tdata2_bypass
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tcontrol_bypass
add wave -noupdate -group WRAPPER -group SOC -group EXECUTION3 -group CSR -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_execution/i_cs_reg_file/tselect_safe
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/clk_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/stall_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/fe_flush_cache_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/lx_dres_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/lx_dreq_o
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/me_data_o
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/dmiss_stall_o
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/fencei_stall_o
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/me_data_req_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/ex_data_req_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/dcache_req
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/dcache_res
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/rd_data
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/uncached
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/mem_txn_active
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/mem_req_fire
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/ex_valid_q
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/ex_addr_q
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/ex_rw_q
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/ex_rw_size_q
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/req_changed
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/selected_byte
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/selected_halfword
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/clk_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/flush_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/cache_req_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/lowX_res_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/cache_res_o
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/lowX_req_o
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/fencei_stall_o
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/CACHE_SIZE
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/BLK_SIZE
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/XLEN
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/NUM_WAY
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/NUM_SET
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/IDX_WIDTH
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/BOFFSET
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/WOFFSET
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/TAG_SIZE
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/flush
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/flush_index
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/cache_req_q
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/rd_idx
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/wr_idx
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/cache_idx
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/cache_miss
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/cache_hit
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/updated_node
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/cache_valid_vec
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/cache_hit_vec
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/evict_way
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/cache_select_data
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/cache_wr_way
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/cache_wr_en
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/lookup_ack
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/dsram
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/tsram
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/nsram
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/dirty_wr_idx
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/dirty_wr_way
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/dirty_wr_en
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/dirty_wr_val
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/dirty_read_vec
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/lowx_req_q
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/lowx_req_valid_q
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/dirty_idx_temp
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/dirty_rw_en_temp
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/dirty_way_temp
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/dirty_wdirty_temp
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/mask_data
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/data_array_wr_en
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/data_wr_pre
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/tag_array_wr_en
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/word_idx
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/write_back
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/evict_tag
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/evict_data
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/fi_active
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/fi_writeback_req
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/fi_mark_clean
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/fi_evict_tag
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/fi_evict_data
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/fi_evict_addr
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/fi_way_onehot
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/fi_set_idx_q
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group DCACHE -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory/i_dcache/dirty_reg
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/clk_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/stb_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/adr_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/byte_sel_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/we_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/dat_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/dat_o
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/uart_rx_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/uart_tx_o
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/baud_div
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/tx_en
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/tx_full
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/tx_empty
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/tx_we
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/rx_en
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/dout
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/rx_full
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/rx_empty
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/rx_re
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/DATA_WIDTH
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/FIFO_DEPTH
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/clk_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/baud_div_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/tx_we_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/tx_en_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/din_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/full_o
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/empty_o
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/tx_bit_o
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/data
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/frame
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/bit_counter
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/baud_counter
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/baud_clk
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/rd_en
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/state
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_TX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_tx/next_state
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/DATA_WIDTH
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/FIFO_DEPTH
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/clk_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/baud_div_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/rx_re_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/rx_en_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/dout_o
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/full_o
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/empty_o
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/rx_bit_i
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/rx_bit_new
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/rx_bit_old
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/baud_counter
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/baud_clk
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/bit_counter
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/rx_we
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/data
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/state
add wave -noupdate -group WRAPPER -group SOC -group MEMORY4 -group UART -group UART_RX -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/i_uart_rx/next_state
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/fe_tracer_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/wr_en_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/rw_size_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/write_data_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/csr_wr_data_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/csr_write_valid_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/rd_addr_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/rd_en_csr_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/wr_en_csr_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/trap_active_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/csr_idx_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/instr_type_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/tcontrol_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/pc_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/flushed_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/clk_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/stall_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/data_sel_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/pc_incr_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/alu_result_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/read_data_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/rf_rw_en_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/rf_rw_en_o
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/wb_data_o
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/fe_flush_cache_i
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/addr_file
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/test_name
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/pass_addr
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/fail_addr
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/addr_check_enabled
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/addr_fd
add wave -noupdate -group WRAPPER -group SOC -group WRITEBACK5 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_writeback/r
add wave -noupdate -group WRAPPER -group SOC -group ARBITER -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory_arbiter/clk_i
add wave -noupdate -group WRAPPER -group SOC -group ARBITER -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory_arbiter/rst_ni
add wave -noupdate -group WRAPPER -group SOC -group ARBITER -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory_arbiter/icache_req_i
add wave -noupdate -group WRAPPER -group SOC -group ARBITER -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory_arbiter/dcache_req_i
add wave -noupdate -group WRAPPER -group SOC -group ARBITER -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory_arbiter/iomem_res_i
add wave -noupdate -group WRAPPER -group SOC -group ARBITER -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory_arbiter/icache_res_o
add wave -noupdate -group WRAPPER -group SOC -group ARBITER -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory_arbiter/dcache_res_o
add wave -noupdate -group WRAPPER -group SOC -group ARBITER -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory_arbiter/iomem_req_o
add wave -noupdate -group WRAPPER -group SOC -group ARBITER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory_arbiter/BOFFSET
add wave -noupdate -group WRAPPER -group SOC -group ARBITER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory_arbiter/round
add wave -noupdate -group WRAPPER -group SOC -group ARBITER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory_arbiter/icache_req_reg
add wave -noupdate -group WRAPPER -group SOC -group ARBITER -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_memory_arbiter/dcache_req_reg
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/r1_addr_de_i
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/r2_addr_de_i
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/r1_addr_ex_i
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/r2_addr_ex_i
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/rd_addr_ex_i
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/pc_sel_ex_i
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/rslt_sel_ex_0
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/rd_addr_me_i
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/rf_rw_me_i
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/rf_rw_wb_i
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/rd_addr_wb_i
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/stall_fe_o
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/stall_de_o
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/flush_de_o
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/flush_ex_o
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/fwd_a_ex_o
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/fwd_b_ex_o
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/fwd_a_de_o
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/fwd_b_de_o
add wave -noupdate -group WRAPPER -group SOC -group HAZARD -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_hazard_unit/lw_stall
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/RESET_VECTOR
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/IC_NUM_SET
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/DC_NUM_SET
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/MAX_FLUSH_CYCLES
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/FLUSH_CNT_WIDTH
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/fe_tracer_o
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/clk_i
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/rst_ni
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/stall_i
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/flush_i
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/flush_pc_i
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/lx_ires_i
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/pc_target_i
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/ex_mtvec_i
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/trap_active_i
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/misa_c_i
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/tdata1_i
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/tdata2_i
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/tcontrol_i
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/spec_hit_i
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/spec_o
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/lx_ireq_o
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/pc_o
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/pc_incr_o
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/inst_o
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/imiss_stall_o
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/exc_type_o
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/de_info_i
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/ex_info_i
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/instr_type_o
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/pc
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/pc_next
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/pc_en
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/fetch_valid
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/fetch_valid_reg
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/uncached
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/uncached_next
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/memregion
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/memregion_next
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/grand
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/grand_next
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/illegal_instr
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/is_comp
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/buff_res
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/buff_req
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/icache_res
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/abuff_icache_req
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/icache_req
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/buff_lowX_res
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/buf_lookup_ack
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/flush_counter
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/flush_in_progress
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/has_debug_breakpoint
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/has_instr_misaligned
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/has_instr_access_fault
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/has_illegal_instr
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/has_ebreak
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/has_ecall
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/trigger0_execute_hit
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/trigger1_execute_hit
add wave -noupdate -group WRAPPER -group WRAPPER -group SOC -group FETCH1 -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_fetch/prev_icache_req_valid
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/clk_i
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/rst_ni
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/addr_i
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/wdata_i
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/wstrb_i
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/rd_en_i
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group in -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/ram_prog_rx_i
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/rdata_o
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/system_reset_o
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group out -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/prog_mode_led_o
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/CACHE_LINE_WIDTH
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/RAM_DEPTH
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/CPU_CLK
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/PROG_BAUD_RATE
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/PROGRAM_SEQUENCE
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/WORD_WIDTH
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/WORDS_PER_LINE
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/BYTES_PER_LINE
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/LINE_DEPTH
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/LINE_ADDR_BITS
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/INIT_FILE_LEN
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/line_addr
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/rdata_q
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/prog_addr
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/prog_data
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/prog_valid
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/prog_mode
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/prog_sys_rst
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/wr_addr
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/wr_data
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/wr_strb
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/init_file
add wave -noupdate -group WRAPPER -group {MAIN MEMORY} -group internal -radix hexadecimal /tb_wrapper/level_wrapper/i_main_ram/fd
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/clk_i
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/rst_ni
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/stb_i
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/adr_i
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/byte_sel_i
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/we_i
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/dat_i
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/dat_o
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/uart_rx_i
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/uart_tx_o
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/baud_div
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/tx_en
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/tx_full
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/tx_empty
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/tx_we
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/rx_en
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/dout
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/rx_full
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/rx_empty
add wave -noupdate -group WRAPPER -group UART -radix hexadecimal /tb_wrapper/level_wrapper/i_uart/rx_re
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/BURST_LEN
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/BEAT_CNT_W
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/clk_i
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/rst_ni
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/iomem_req_i
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/iomem_res_o
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/wb_m_o
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/wb_s_i
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/state_q
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/state_d
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/addr_q
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/wdata_q
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/rdata_q
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/beat_cnt_q
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/byte_sel_q
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/write_q
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/uncached_q
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/is_write
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/is_uncached
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/wdata_packed
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/byte_sel_comb
add wave -noupdate -group WRAPPER -group WB_MASTER -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_master/word_offset
add wave -noupdate -group WRAPPER -group WB_INTERCON -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_interconnect/NUM_SLAVES
add wave -noupdate -group WRAPPER -group WB_INTERCON -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_interconnect/SLAVE_RAM
add wave -noupdate -group WRAPPER -group WB_INTERCON -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_interconnect/SLAVE_CLINT
add wave -noupdate -group WRAPPER -group WB_INTERCON -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_interconnect/SLAVE_PBUS
add wave -noupdate -group WRAPPER -group WB_INTERCON -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_interconnect/clk_i
add wave -noupdate -group WRAPPER -group WB_INTERCON -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_interconnect/rst_ni
add wave -noupdate -group WRAPPER -group WB_INTERCON -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_interconnect/wb_m_i
add wave -noupdate -group WRAPPER -group WB_INTERCON -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_interconnect/wb_s_o
add wave -noupdate -group WRAPPER -group WB_INTERCON -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_interconnect/wb_m_o
add wave -noupdate -group WRAPPER -group WB_INTERCON -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_interconnect/wb_s_i
add wave -noupdate -group WRAPPER -group WB_INTERCON -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_interconnect/slave_sel
add wave -noupdate -group WRAPPER -group WB_INTERCON -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_interconnect/addr_valid
add wave -noupdate -group WRAPPER -group WB_INTERCON -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_interconnect/active_slave_q
add wave -noupdate -group WRAPPER -group WB_INTERCON -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_interconnect/req_pending_q
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/CLINT_MSIP
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/CLINT_MTIMECMP_LO
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/CLINT_MTIMECMP_HI
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/CLINT_MTIME_LO
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/CLINT_MTIME_HI
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/clk_i
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/rst_ni
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/wb_m_i
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/wb_s_o
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/timer_irq_o
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/sw_irq_o
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/mtime_q
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/mtimecmp_q
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/msip_q
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/req_valid
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/req_we
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/reg_offset
add wave -noupdate -group WRAPPER -group WB_CLINT -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_clint/rdata
add wave -noupdate -group WRAPPER -group WB_PBUS -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_pbus/clk_i
add wave -noupdate -group WRAPPER -group WB_PBUS -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_pbus/rst_ni
add wave -noupdate -group WRAPPER -group WB_PBUS -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_pbus/wb_m_i
add wave -noupdate -group WRAPPER -group WB_PBUS -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_pbus/wb_s_o
add wave -noupdate -group WRAPPER -group WB_PBUS -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_pbus/pbus_addr_o
add wave -noupdate -group WRAPPER -group WB_PBUS -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_pbus/pbus_wdata_o
add wave -noupdate -group WRAPPER -group WB_PBUS -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_pbus/pbus_wstrb_o
add wave -noupdate -group WRAPPER -group WB_PBUS -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_pbus/pbus_valid_o
add wave -noupdate -group WRAPPER -group WB_PBUS -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_pbus/pbus_we_o
add wave -noupdate -group WRAPPER -group WB_PBUS -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_pbus/pbus_rdata_i
add wave -noupdate -group WRAPPER -group WB_PBUS -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_pbus/pbus_ready_i
add wave -noupdate -group WRAPPER -group WB_PBUS -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_pbus/req_valid
add wave -noupdate -group WRAPPER -group WB_PBUS -radix hexadecimal /tb_wrapper/level_wrapper/i_wb_pbus/req_we
add wave -noupdate -divider -height 20 {=============== QUICK DEBUG ===============}
add wave -noupdate -group QUICK_DEBUG -group Clock/Reset -color Gold /tb_wrapper/clk_i
add wave -noupdate -group QUICK_DEBUG -group Clock/Reset -color Orange /tb_wrapper/rst_ni
add wave -noupdate -group QUICK_DEBUG -group {PC Progress} -color Cyan -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/fe_pc
add wave -noupdate -group QUICK_DEBUG -group {PC Progress} -color Green -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/pipe1.pc
add wave -noupdate -group QUICK_DEBUG -group {PC Progress} -color Yellow -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/pipe2.pc
add wave -noupdate -group QUICK_DEBUG -group {PC Progress} -color Magenta -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/pipe3.pc
add wave -noupdate -group QUICK_DEBUG -group {PC Progress} -color Red -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/pipe4.pc
add wave -noupdate -group QUICK_DEBUG -group Instructions -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/fe_inst
add wave -noupdate -group QUICK_DEBUG -group Instructions -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/pipe1.inst
add wave -noupdate -group QUICK_DEBUG -group Instructions /tb_wrapper/level_wrapper/i_soc/fe_instr_type
add wave -noupdate -group QUICK_DEBUG -group Instructions /tb_wrapper/level_wrapper/i_soc/pipe1.instr_type
add wave -noupdate -group QUICK_DEBUG -group Instructions /tb_wrapper/level_wrapper/i_soc/pipe2.instr_type
add wave -noupdate -group QUICK_DEBUG -group Stalls -color Red /tb_wrapper/level_wrapper/i_soc/stall_cause
add wave -noupdate -group QUICK_DEBUG -group Stalls -color Orange /tb_wrapper/level_wrapper/i_soc/fe_imiss_stall
add wave -noupdate -group QUICK_DEBUG -group Stalls -color Orange /tb_wrapper/level_wrapper/i_soc/me_dmiss_stall
add wave -noupdate -group QUICK_DEBUG -group Stalls -color Orange /tb_wrapper/level_wrapper/i_soc/ex_alu_stall
add wave -noupdate -group QUICK_DEBUG -group Exceptions -color Red /tb_wrapper/level_wrapper/i_soc/trap_active
add wave -noupdate -group QUICK_DEBUG -group Exceptions /tb_wrapper/level_wrapper/i_soc/excp_mask
add wave -noupdate -group QUICK_DEBUG -group Exceptions /tb_wrapper/level_wrapper/i_soc/priority_flush
add wave -noupdate -group QUICK_DEBUG -group {Register File} -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/i_decode/i_reg_file/registers
add wave -noupdate -group QUICK_DEBUG -group Inputs -color Gold /tb_wrapper/level_wrapper/i_soc/clk_i
add wave -noupdate -group QUICK_DEBUG -group Inputs -color Orange /tb_wrapper/level_wrapper/i_soc/rst_ni
add wave -noupdate -group QUICK_DEBUG -group Inputs -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/iomem_res_i
add wave -noupdate -group QUICK_DEBUG -group Outputs -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/iomem_req_o
add wave -noupdate -group QUICK_DEBUG -group {Pipeline Registers} -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/pipe1
add wave -noupdate -group QUICK_DEBUG -group {Pipeline Registers} -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/pipe2
add wave -noupdate -group QUICK_DEBUG -group {Pipeline Registers} -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/pipe3
add wave -noupdate -group QUICK_DEBUG -group {Pipeline Registers} -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/pipe4
add wave -noupdate -group QUICK_DEBUG -group {Stall/Flush Control} /tb_wrapper/level_wrapper/i_soc/stall_cause
add wave -noupdate -group QUICK_DEBUG -group {Stall/Flush Control} /tb_wrapper/level_wrapper/i_soc/fe_imiss_stall
add wave -noupdate -group QUICK_DEBUG -group {Stall/Flush Control} /tb_wrapper/level_wrapper/i_soc/me_dmiss_stall
add wave -noupdate -group QUICK_DEBUG -group {Stall/Flush Control} /tb_wrapper/level_wrapper/i_soc/ex_alu_stall
add wave -noupdate -group QUICK_DEBUG -group {Stall/Flush Control} /tb_wrapper/level_wrapper/i_soc/me_fencei_stall
add wave -noupdate -group QUICK_DEBUG -group {Stall/Flush Control} /tb_wrapper/level_wrapper/i_soc/de_flush
add wave -noupdate -group QUICK_DEBUG -group {Stall/Flush Control} /tb_wrapper/level_wrapper/i_soc/ex_flush
add wave -noupdate -group QUICK_DEBUG -group {Stall/Flush Control} /tb_wrapper/level_wrapper/i_soc/fencei_flush
add wave -noupdate -group QUICK_DEBUG -group {Stall/Flush Control} /tb_wrapper/level_wrapper/i_soc/priority_flush
add wave -noupdate -group QUICK_DEBUG -group {Exception Handling} /tb_wrapper/level_wrapper/i_soc/trap_active
add wave -noupdate -group QUICK_DEBUG -group {Exception Handling} /tb_wrapper/level_wrapper/i_soc/fe_trap_active
add wave -noupdate -group QUICK_DEBUG -group {Exception Handling} /tb_wrapper/level_wrapper/i_soc/de_trap_active
add wave -noupdate -group QUICK_DEBUG -group {Exception Handling} /tb_wrapper/level_wrapper/i_soc/excp_mask
add wave -noupdate -group QUICK_DEBUG -group {Exception Handling} -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/trap_tval
add wave -noupdate -group QUICK_DEBUG -group {Exception Handling} /tb_wrapper/level_wrapper/i_soc/fe_exc_type
add wave -noupdate -group QUICK_DEBUG -group {Exception Handling} /tb_wrapper/level_wrapper/i_soc/de_exc_type
add wave -noupdate -group QUICK_DEBUG -group {Exception Handling} /tb_wrapper/level_wrapper/i_soc/ex_exc_type
add wave -noupdate -group QUICK_DEBUG -group {Exception Handling} /tb_wrapper/level_wrapper/i_soc/ex_alu_exc_type
add wave -noupdate -group QUICK_DEBUG -group {Exception Handling} -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_trap_cause
add wave -noupdate -group QUICK_DEBUG -group {Exception Handling} -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_trap_mepc
add wave -noupdate -group QUICK_DEBUG -group {Exception Handling} -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_mtvec
add wave -noupdate -group QUICK_DEBUG -group {Branch Prediction} /tb_wrapper/level_wrapper/i_soc/ex_spec_hit
add wave -noupdate -group QUICK_DEBUG -group {Branch Prediction} /tb_wrapper/level_wrapper/i_soc/ex_pc_sel
add wave -noupdate -group QUICK_DEBUG -group {Branch Prediction} -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_pc_target
add wave -noupdate -group QUICK_DEBUG -group {Branch Prediction} -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_pc_target_last
add wave -noupdate -group QUICK_DEBUG -group {Branch Prediction} /tb_wrapper/level_wrapper/i_soc/fe_spec
add wave -noupdate -group QUICK_DEBUG -group {Data Request} -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/ex_data_req
add wave -noupdate -group QUICK_DEBUG -group {Data Request} -radix hexadecimal /tb_wrapper/level_wrapper/i_soc/me_data_req
add wave -noupdate -group QUICK_DEBUG -group Forwarding /tb_wrapper/level_wrapper/i_soc/de_fwd_a
add wave -noupdate -group QUICK_DEBUG -group Forwarding /tb_wrapper/level_wrapper/i_soc/de_fwd_b
add wave -noupdate -group QUICK_DEBUG -group Forwarding /tb_wrapper/level_wrapper/i_soc/ex_fwd_a
add wave -noupdate -group QUICK_DEBUG -group Forwarding /tb_wrapper/level_wrapper/i_soc/ex_fwd_b
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/clk_i
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/rst_ni
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/flush_i
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/l1_req_i
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/l1_res_o
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mem_req_o
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mem_res_i
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/pipe_state
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/pipe_set_index
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/pipe_req_tag
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/pipe_offset
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/pipe_req_valid
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/pipe_req_is_write
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/pipe_req_wdata
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/pipe_req_wstrb
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/pipe_req_addr
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/l1_req_accept
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/pipeline_busy
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/tag_rd_data
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/valid_rd
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/dirty_rd
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mesi_rd
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/hit_any
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/hit_way_oh
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/hit_way_bin
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/victim_way
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/data_rd
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/evict_data
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mshr_full
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mshr_alloc_idx
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mshr_alloc_merged
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mshr_pending_valid
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mshr_pending_addr
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mshr_pending_is_write
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mshr_pending_issued
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mshr_resp_valid
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mshr_resp_idx
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mshr_resp_is_write
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mshr_resp_wdata
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mshr_resp_wstrb
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mshr_resp_accepted
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mshr_wb_valid
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mshr_wb_addr
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/mshr_valid_vec
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/master_fill_req_valid
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/master_fill_req_addr
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/master_fill_resp_valid
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/master_fill_resp_data
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/master_fill_req_issued
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/master_wb_req_valid
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/master_wb_req_addr
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/master_wb_req_data
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/master_wb_done
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/master_busy
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/flush_done
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/req_set_q
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/req_tag_q
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/req_addr_q
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/req_is_write_q
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/req_wdata_q
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/req_wstrb_q
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/evict_dirty
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/evict_tag
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/evict_addr
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/ev_read_hit
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/ev_read_miss
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/ev_write_hit
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/ev_write_miss
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/ev_writeback
add wave -noupdate -group L2_CACHE /tb_wrapper/level_wrapper/i_soc/i_l2_cache/ev_mshr_stall
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_decoder/clk_i
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_decoder/rst_ni
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_decoder/l1_req_i
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_decoder/l1_req_accept
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_decoder/pipe_set_index
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_decoder/pipe_req_tag
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_decoder/pipe_offset
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_decoder/pipe_req_valid
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_decoder/pipe_req_is_write
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_decoder/pipe_req_wdata
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_decoder/pipe_req_wstrb
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_decoder/pipe_req_addr
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_decoder/mshr_full
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_decoder/pipeline_busy
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/NUM_SETS
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/WAYS
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/TAG_BITS
add wave -noupdate -group L2_CACHE -group Decoder /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/INDEX_BITS
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/clk_i
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/rst_ni
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/rd_index
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/rd_en
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/tag_rd_data
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/valid_rd
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/dirty_rd
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/mesi_rd
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/wr_en
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/wr_index
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/wr_way
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/wr_tag
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/wr_valid
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/wr_dirty
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/wr_mesi
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/dirty_wr_en
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/dirty_wr_index
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/dirty_wr_way
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/flush_req
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/flush_done
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/tag_ram
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/flush_state
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_tag_array/flush_set_cnt
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/NUM_SETS
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/WAYS
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/NUM_BANKS
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/BANK_BITS
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/BANK_SETS
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/SRAM_DEPTH
add wave -noupdate -group L2_CACHE -group TAG_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/SRAM_AW
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/clk_i
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/rst_ni
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/rd_index
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/rd_way
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/rd_en
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/rd_data
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/wr_index
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/wr_way
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/wr_data
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/wr_strb
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/wr_en
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/fill_en
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/fill_index
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/fill_way
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/fill_data
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/evict_rd_index
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/evict_rd_way
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/evict_rd_en
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/evict_rd_data
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/sram
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_data_array/#ublk#182267977#78/merged
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_hit_miss/WAYS
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_hit_miss/TAG_BITS
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_hit_miss/req_tag
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_hit_miss/tag_rd_data
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_hit_miss/valid_bit
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_hit_miss/hit_any
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_hit_miss/hit_way_oh
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_hit_miss/hit_way_bin
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_lru/NUM_SETS
add wave -noupdate -group L2_CACHE -group DATA_ARRAY /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_lru/WAYS
add wave -noupdate -group L2_CACHE -group LRU /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_lru/clk_i
add wave -noupdate -group L2_CACHE -group LRU /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_lru/rst_ni
add wave -noupdate -group L2_CACHE -group LRU /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_lru/access_valid
add wave -noupdate -group L2_CACHE -group LRU /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_lru/access_set
add wave -noupdate -group L2_CACHE -group LRU /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_lru/access_way
add wave -noupdate -group L2_CACHE -group LRU /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_lru/victim_set
add wave -noupdate -group L2_CACHE -group LRU /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_lru/victim_way
add wave -noupdate -group L2_CACHE -group LRU /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_lru/plru_reg
add wave -noupdate -group L2_CACHE -group LRU /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/DEPTH
add wave -noupdate -group L2_CACHE -group LRU /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/LINE_ADDR_W
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/clk_i
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/rst_ni
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/alloc_req
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/alloc_addr
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/alloc_is_write
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/alloc_wdata
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/alloc_wstrb
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/alloc_idx
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/alloc_merged
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/full
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/fill_valid
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/fill_addr
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/pending_valid
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/pending_addr
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/pending_is_write
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/pending_issued
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/resp_valid
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/resp_idx
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/resp_is_write
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/resp_wdata
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/resp_wstrb
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/resp_accepted
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/wb_entry_valid
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/wb_entry_addr
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/wb_done
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/mshr_valid_vec
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/mshr
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/line_match
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/any_match
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/match_idx
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/free_vec
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/free_idx
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/any_free
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/fill_match_vec
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/fill_entry_idx
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/pending_vec
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/pending_idx
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/complete_vec
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/wb_vec
add wave -noupdate -group L2_CACHE -group MSHR /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_mshr/wb_idx
add wave -noupdate -group L2_CACHE -group MASTER /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_master/clk_i
add wave -noupdate -group L2_CACHE -group MASTER /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_master/rst_ni
add wave -noupdate -group L2_CACHE -group MASTER /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_master/mem_req_o
add wave -noupdate -group L2_CACHE -group MASTER /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_master/mem_res_i
add wave -noupdate -group L2_CACHE -group MASTER /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_master/fill_req_valid
add wave -noupdate -group L2_CACHE -group MASTER /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_master/fill_req_addr
add wave -noupdate -group L2_CACHE -group MASTER /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_master/fill_resp_valid
add wave -noupdate -group L2_CACHE -group MASTER /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_master/fill_resp_data
add wave -noupdate -group L2_CACHE -group MASTER /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_master/fill_req_issued
add wave -noupdate -group L2_CACHE -group MASTER /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_master/wb_req_valid
add wave -noupdate -group L2_CACHE -group MASTER /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_master/wb_req_addr
add wave -noupdate -group L2_CACHE -group MASTER /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_master/wb_req_data
add wave -noupdate -group L2_CACHE -group MASTER /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_master/wb_done
add wave -noupdate -group L2_CACHE -group MASTER /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_master/busy
add wave -noupdate -group L2_CACHE -group MASTER /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_master/state
add wave -noupdate -group L2_CACHE -group MASTER /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_master/req_addr_q
add wave -noupdate -group L2_CACHE -group MASTER /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_master/req_data_q
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/clk_i
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/rst_ni
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/ev_read_hit
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/ev_read_miss
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/ev_write_hit
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/ev_write_miss
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/ev_writeback
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/ev_mshr_stall
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/perf_hit_count
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/perf_miss_count
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/perf_wb_count
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/perf_stall_count
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/cnt_rd_hit
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/cnt_rd_miss
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/cnt_wr_hit
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/cnt_wr_miss
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/cnt_wb
add wave -noupdate -group L2_CACHE -group PERF /tb_wrapper/level_wrapper/i_soc/i_l2_cache/u_perf/cnt_stall
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {1895 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 250
configure wave -valuecolwidth 50
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
update
WaveRestoreZoom {0 ns} {37763 ns}
