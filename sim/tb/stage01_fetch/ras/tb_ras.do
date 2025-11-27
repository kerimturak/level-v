onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group TB -radix hexadecimal /tb_ras/clk
add wave -noupdate -expand -group TB -radix hexadecimal /tb_ras/rst_ni
add wave -noupdate -expand -group TB -radix hexadecimal /tb_ras/restore_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_ras/restore_pc_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_ras/req_valid_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_ras/j_type_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_ras/jr_type_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_ras/rd_addr_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_ras/r1_addr_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_ras/return_addr_i
add wave -noupdate -expand -group TB -radix hexadecimal /tb_ras/popped_addr_o
add wave -noupdate -expand -group TB -radix hexadecimal /tb_ras/predict_valid_o
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_ras/uut/RAS_SIZE
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_ras/uut/clk_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_ras/uut/rst_ni
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_ras/uut/restore_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_ras/uut/restore_pc_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_ras/uut/req_valid_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_ras/uut/j_type_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_ras/uut/jr_type_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_ras/uut/rd_addr_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_ras/uut/r1_addr_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_ras/uut/return_addr_i
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_ras/uut/popped_addr_o
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_ras/uut/predict_valid_o
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_ras/uut/ras
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_ras/uut/ras_op
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_ras/uut/link_rd
add wave -noupdate -expand -group RAS -radix hexadecimal /tb_ras/uut/link_r1
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {134301 ps} 0}
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
WaveRestoreZoom {134050 ps} {135050 ps}
