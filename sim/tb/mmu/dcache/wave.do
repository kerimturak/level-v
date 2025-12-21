onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -divider {Clock and Reset}
add wave -noupdate /tb_dcache_writeback/clk
add wave -noupdate /tb_dcache_writeback/rst_n
add wave -noupdate -divider {Cache Request Interface}
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/clk_i
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/rst_ni
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/flush_i
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/cache_req_i
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/cache_res_o
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/lowX_res_i
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/lowX_req_o
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/fencei_stall_o
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/flush
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/flush_index
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/cache_req_q
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/rd_idx
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/wr_idx
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/cache_idx
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/cache_miss
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/cache_hit
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/updated_node
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/cache_valid_vec
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/cache_hit_vec
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/evict_way
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/cache_select_data
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/cache_wr_way
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/cache_wr_en
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/lookup_ack
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/dsram
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/tsram
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/nsram
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/drsram_wr_idx
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/drsram_wr_way
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/drsram_wr_rw_en
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/drsram_wr_wdirty
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/drsram_rd_rdirty
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/drsram_idx_temp
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/drsram_rw_en_temp
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/drsram_way_temp
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/drsram_wdirty_temp
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/mask_data
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/data_array_wr_en
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/data_wr_pre
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/tag_array_wr_en
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/word_idx
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/write_back
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/evict_tag
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/evict_data
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/wb_state_q
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/wb_state_d
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/wb_evict_tag_q
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/wb_evict_data_q
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/wb_evict_idx_q
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/wb_evict_way_q
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/wb_active
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/fi_state_q
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/fi_state_d
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/fi_set_idx_q
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/fi_set_idx_d
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/fi_way_idx_q
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/fi_way_idx_d
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/fi_active
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/fi_writeback_req
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/fi_evict_tag
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/fi_evict_data
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/fi_evict_addr
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/fi_mark_clean
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/fi_way_onehot
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/fi_has_dirty
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/flush_i_prev
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/node_q
add wave -noupdate -radix hexadecimal /tb_dcache_writeback/dut/fi_start
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
quietly wave cursor active 0
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
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
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {1 ns}
