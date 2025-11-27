onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group TB -radix hexadecimal /tb_align_buffer/clk
add wave -noupdate -expand -group TB -radix hexadecimal /tb_align_buffer/rst_n
add wave -noupdate -expand -group TB -radix hexadecimal /tb_align_buffer/flush
add wave -noupdate -expand -group TB -radix hexadecimal /tb_align_buffer/buff_req
add wave -noupdate -expand -group TB -radix hexadecimal /tb_align_buffer/buff_res
add wave -noupdate -expand -group TB -radix hexadecimal /tb_align_buffer/lowX_res
add wave -noupdate -expand -group TB -radix hexadecimal /tb_align_buffer/lowX_req
add wave -noupdate -expand -group TB -radix hexadecimal /tb_align_buffer/lowX_response_pending
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/CACHE_SIZE
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/BLK_SIZE
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/XLEN
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/NUM_WAY
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/DATA_WIDTH
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/NUM_SET
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/IDX_WIDTH
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/BOFFSET
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/WOFFSET
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/TAG_SIZE
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/clk_i
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/rst_ni
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/flush_i
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/buff_req_i
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/buff_res_o
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/lowX_res_i
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/lowX_req_o
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/even
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/odd
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/miss_state
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/hit_state
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/wr_idx
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/tag_wr_en
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/data_wr_en
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/wr_tag
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/ebram
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/obram
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/tag_ram
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/word_sel
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/parcel_idx
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/overflow
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/unalign
add wave -noupdate -expand -group ALIGN_BUFFER -radix hexadecimal /tb_align_buffer/dut/lookup_ack
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {294 ps} 0}
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
WaveRestoreZoom {0 ps} {1 ns}
