onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group TB -radix hexadecimal /tb_icache/CACHE_SIZE
add wave -noupdate -expand -group TB -radix hexadecimal /tb_icache/BLK_SIZE
add wave -noupdate -expand -group TB -radix hexadecimal /tb_icache/XLEN
add wave -noupdate -expand -group TB -radix hexadecimal /tb_icache/NUM_WAY
add wave -noupdate -expand -group TB -radix hexadecimal /tb_icache/NUM_SET
add wave -noupdate -expand -group TB -radix hexadecimal /tb_icache/IDX_WIDTH
add wave -noupdate -expand -group TB -radix hexadecimal /tb_icache/clk
add wave -noupdate -expand -group TB -radix hexadecimal /tb_icache/rst_ni
add wave -noupdate -expand -group TB -radix hexadecimal /tb_icache/flush_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_icache/cache_req_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_icache/cache_res_o
add wave -noupdate -expand -group TB -radix hexadecimal /tb_icache/lowX_res_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_icache/lowX_req_o
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/IS_ICACHE
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/CACHE_SIZE
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/BLK_SIZE
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/XLEN
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/NUM_WAY
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/NUM_SET
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/IDX_WIDTH
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/BOFFSET
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/WOFFSET
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/TAG_SIZE
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/clk_i
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/rst_ni
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/flush_i
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/cache_req_i
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/cache_res_o
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/lowX_res_i
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/lowX_req_o
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/flush
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/flush_index
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/cache_req_q
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/rd_idx
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/wr_idx
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/cache_idx
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/cache_miss
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/cache_hit
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/updated_node
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/cache_valid_vec
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/cache_hit_vec
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/evict_way
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/cache_select_data
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/cache_wr_way
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/cache_wr_en
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/lookup_ack
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/dsram
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/tsram
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/nsram
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/drsram
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/mask_data
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/data_array_wr_en
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/data_wr_pre
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/tag_array_wr_en
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/word_idx
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/write_back
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/evict_tag
add wave -noupdate -expand -group ICACHE -radix hexadecimal /tb_icache/dut/evict_data
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {39907 ps} 0}
quietly wave cursor active 1
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
WaveRestoreZoom {775175 ps} {848675 ps}
