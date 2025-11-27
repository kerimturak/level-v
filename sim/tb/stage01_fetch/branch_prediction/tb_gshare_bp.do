onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group TB -radix hexadecimal /tb_gshare_bp/clk
add wave -noupdate -expand -group TB -radix hexadecimal /tb_gshare_bp/rst_ni
add wave -noupdate -expand -group TB -radix hexadecimal /tb_gshare_bp/spec_hit_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_gshare_bp/stall_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_gshare_bp/is_comp_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_gshare_bp/inst_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_gshare_bp/pc_target_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_gshare_bp/pc_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_gshare_bp/pc2_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_gshare_bp/pc4_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_gshare_bp/fetch_valid_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_gshare_bp/spec_o
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/clk_i
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/rst_ni
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/spec_hit_i
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/stall_i
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/is_comp_i
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/inst_i
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/pc_target_i
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/pc_i
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/pc2_i
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/pc4_i
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/fetch_valid_i
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/spec_o
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/imm
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/j_type
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/jr_type
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/b_type
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/ras_taken
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/ras_taken_q
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/req_valid
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/popped_addr
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/pushed_addr
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/stage_pc
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/branch_q
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/taken_q
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/branch
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/ghr
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/pht
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/btb_target
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/btb_pc
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/pht_rd_idx
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/pht_wr_idx
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/btb_rd_idx
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/btb_wr_idx
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/pht_ptr
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/pht_bit1
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/ex_taken
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/restore_ras
add wave -noupdate -expand -group GSHARE -radix hexadecimal /tb_gshare_bp/dut/restore_pc
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_gshare_bp/dut/ras/RAS_SIZE
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_gshare_bp/dut/ras/clk_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_gshare_bp/dut/ras/rst_ni
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_gshare_bp/dut/ras/restore_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_gshare_bp/dut/ras/restore_pc_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_gshare_bp/dut/ras/req_valid_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_gshare_bp/dut/ras/j_type_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_gshare_bp/dut/ras/jr_type_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_gshare_bp/dut/ras/rd_addr_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_gshare_bp/dut/ras/r1_addr_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_gshare_bp/dut/ras/return_addr_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_gshare_bp/dut/ras/popped_addr_o
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_gshare_bp/dut/ras/predict_valid_o
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_gshare_bp/dut/ras/ras
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_gshare_bp/dut/ras/ras_op
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_gshare_bp/dut/ras/link_rd
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_gshare_bp/dut/ras/link_r1
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {176 ps} 0}
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
