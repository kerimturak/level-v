// ceres RISC-V Processor
// Copyright (c) 2024 Kerim TURAK
// Permission is hereby granted, free of charge, to any person obtaining a copy of this software
// and associated documentation files (the "Software"), to deal in the Software without restriction,
// including without limitation the rights to use, copy, modify, merge, publish, distribute,
// sublicense, and/or sell copies of the Software, and to permit persons to whom the Software
// is furnished to do so, subject to the following conditions:
// The above copyright notice and this permission notice shall be included in all copies or
// substantial portions of the Software.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Kerim TURAK - kerimturak@hotmail.com                       //
//                                                                            //
// Additional contributions by:                                               //
//                 --                                                         //
//                                                                            //
// Design Name:    stage5_writeback                                           //
// Project Name:   ceres                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    stage5_writeback                                           //
////////////////////////////////////////////////////////////////////////////////

`timescale 1ns / 1ps
`include "ceres_defines.svh"
module writeback
  import ceres_param::*;
(
`ifdef TRACER_EN
    input  fe_tracer_info_t            fe_tracer_i,
    input  logic                       wr_en_i,
    input  logic            [     1:0] rw_size_i,
    input  logic            [XLEN-1:0] write_data_i,
    input  logic            [XLEN-1:0] csr_wr_data_i,
    input  logic            [     4:0] rd_addr_i,
    input  logic                       rd_en_csr_i,
    input  logic                       wr_en_csr_i,
    input  logic                       trap_active_i,
    input  logic            [    11:0] csr_idx_i,
    input  instr_type_e                instr_type_i,
`endif
    input  logic                       clk_i,
    input  logic                       rst_ni,
    input  stall_e                     stall_i,
    input  logic            [     1:0] data_sel_i,
    input  logic            [XLEN-1:0] pc_incr_i,
    input  logic            [XLEN-1:0] pc_i,
    input  logic            [XLEN-1:0] alu_result_i,
    input  logic            [XLEN-1:0] read_data_i,
    input  logic                       rf_rw_en_i,
    output logic                       rf_rw_en_o,
    output logic            [XLEN-1:0] wb_data_o,
    input  logic                       fe_flush_cache_i
);

  always_comb begin
    rf_rw_en_o = rf_rw_en_i && !fe_flush_cache_i && !(stall_i inside {IMISS_STALL, DMISS_STALL, ALU_STALL});
    wb_data_o  = data_sel_i[1] ? pc_incr_i : (data_sel_i[0] ? read_data_i : alu_result_i);
  end

`ifdef TRACER_EN
  `include "writeback_log.svh"
`endif

endmodule
