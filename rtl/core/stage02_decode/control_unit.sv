/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
`include "ceres_defines.svh"
module control_unit
  import ceres_param::*;
(
    input  inst_t       inst_i,
    input  instr_type_e instr_type_i,
    output ctrl_t       ctrl_o
);

  logic illegal_shift;

  // CSR illegal detection -------------------------------------------------

  logic csr_supported;
  logic csr_write_intent;
  logic instr_is_csr;
  logic csr_read_only;

  always_comb begin
    illegal_shift = 1'b0;

    if (instr_type_i == i_slli || instr_type_i == i_srli || instr_type_i == i_srai) begin
      // RV32: imm[5] must be zero
      if (inst_i[25]) begin
        illegal_shift = 1'b1;
      end
    end


    // CSR instruction mı?
    instr_is_csr = (instr_type_i == CSR_RW) || (instr_type_i == CSR_RWI) || (instr_type_i == CSR_RS) || (instr_type_i == CSR_RSI) || (instr_type_i == CSR_RC) || (instr_type_i == CSR_RCI);
    // CSR adresi core tarafından destekleniyor mu?
    csr_supported = is_supported_csr(inst_i[31:20]);
    // Yazma niyeti var mı?
    // CSR read-only mı? (CSR address bits [11:10] == 2'b11 means read-only)
    csr_read_only = (inst_i[31:30] == 2'b11);
    csr_write_intent =
       (instr_type_i == CSR_RW)  ||
       (instr_type_i == CSR_RWI) ||
       ((instr_type_i == CSR_RS  || instr_type_i == CSR_RC)  && inst_i.r1_addr != 5'd0) ||
       ((instr_type_i == CSR_RSI || instr_type_i == CSR_RCI) && inst_i[19:15] != 5'd0);
    // Exception type hesaplama
    ctrl_o.exc_type = NO_EXCEPTION;
    // Önce shift illegal kontrolü
    if (illegal_shift) begin
      ctrl_o.exc_type = ILLEGAL_INSTRUCTION;
    end else if (instr_is_csr && !csr_supported) begin
      // cycle/cycleh/instret alias (C00/C02/C80/C82) burada yakalanacak
      ctrl_o.exc_type = ILLEGAL_INSTRUCTION;
    end else if (instr_is_csr && csr_read_only && csr_write_intent) begin
      // Read-only CSR'ye yazma girişimi illegal instruction
      ctrl_o.exc_type = ILLEGAL_INSTRUCTION;
    end


    ctrl_o.alu_in1_sel = instr_type_i == u_auipc ? 2'd2 : (instr_type_i == i_jalr ? 2'b1 : 2'b0);
    ctrl_o.ld_op_sign  = !(instr_type_i == i_lhu || instr_type_i == i_lbu) && (instr_type_i == i_lh || instr_type_i == i_lb);
    case (instr_type_i)
      r_add, i_lb, i_lh, i_lw, i_lbu, i_lhu, i_addi, s_sb, s_sh, s_sw, b_beq, b_bne, b_blt, b_bge, b_bltu, b_bgeu, u_jal, i_jalr: ctrl_o.alu_ctrl = OP_ADD;
      r_sub:                                                                                                                      ctrl_o.alu_ctrl = OP_SUB;
      r_sll, i_slli:                                                                                                              ctrl_o.alu_ctrl = OP_SLL;
      r_slt, i_slti:                                                                                                              ctrl_o.alu_ctrl = OP_SLT;
      r_sltu, i_sltiu:                                                                                                            ctrl_o.alu_ctrl = OP_SLTU;
      r_xor, i_xori:                                                                                                              ctrl_o.alu_ctrl = OP_XOR;
      r_srl, i_srli:                                                                                                              ctrl_o.alu_ctrl = OP_SRL;
      r_sra, i_srai:                                                                                                              ctrl_o.alu_ctrl = OP_SRA;
      r_or, i_ori:                                                                                                                ctrl_o.alu_ctrl = OP_OR;
      r_and, i_andi:                                                                                                              ctrl_o.alu_ctrl = OP_AND;
      r_mul:                                                                                                                      ctrl_o.alu_ctrl = OP_MUL;
      r_mulh:                                                                                                                     ctrl_o.alu_ctrl = OP_MULH;
      r_mulhsu:                                                                                                                   ctrl_o.alu_ctrl = OP_MULHSU;
      r_mulhu:                                                                                                                    ctrl_o.alu_ctrl = OP_MULHU;
      r_div:                                                                                                                      ctrl_o.alu_ctrl = OP_DIV;
      r_divu:                                                                                                                     ctrl_o.alu_ctrl = OP_DIVU;  // roundin
      r_rem:                                                                                                                      ctrl_o.alu_ctrl = OP_REM;
      r_remu:                                                                                                                     ctrl_o.alu_ctrl = OP_REMU;
      u_lui:                                                                                                                      ctrl_o.alu_ctrl = OP_LUI;
      CSR_RW:                                                                                                                     ctrl_o.alu_ctrl = OP_CSRRW;
      CSR_RS:                                                                                                                     ctrl_o.alu_ctrl = OP_CSRRS;
      CSR_RC:                                                                                                                     ctrl_o.alu_ctrl = OP_CSRRC;
      CSR_RWI:                                                                                                                    ctrl_o.alu_ctrl = OP_CSRRWI;
      CSR_RSI:                                                                                                                    ctrl_o.alu_ctrl = OP_CSRRSI;
      CSR_RCI:                                                                                                                    ctrl_o.alu_ctrl = OP_CSRRCI;
      default:                                                                                                                    ctrl_o.alu_ctrl = OP_ADD;
    endcase

    case (instr_type_i)
      b_beq:   ctrl_o.pc_sel = BEQ;
      b_bne:   ctrl_o.pc_sel = BNE;
      b_blt:   ctrl_o.pc_sel = BLT;
      b_bge:   ctrl_o.pc_sel = BGE;
      b_bltu:  ctrl_o.pc_sel = BLTU;
      b_bgeu:  ctrl_o.pc_sel = BGEU;
      i_jalr:  ctrl_o.pc_sel = JALR;
      u_jal:   ctrl_o.pc_sel = JAL;
      default: ctrl_o.pc_sel = NO_BJ;
    endcase

    case (inst_i.opcode)
      op_r_type: begin
        ctrl_o.rf_rw_en     = 1'b1;
        ctrl_o.csr_or_data  = 1'b0;
        ctrl_o.rd_csr       = 1'b0;
        ctrl_o.wr_csr       = 1'b0;
        ctrl_o.csr_idx      = inst_i[31:20];
        ctrl_o.imm_sel      = NO_IMM;
        ctrl_o.alu_in2_sel  = 1'b0;
        ctrl_o.wr_en        = 1'b0;
        ctrl_o.result_src   = 2'b00;
        ctrl_o.rw_size      = NO_SIZE;
        ctrl_o.dcache_valid = 1'b0;
      end
      op_i_type: begin
        ctrl_o.rf_rw_en    = 1'b1;
        ctrl_o.csr_or_data = 1'b0;
        ctrl_o.rd_csr      = 1'b0;
        ctrl_o.wr_csr      = 1'b0;
        ctrl_o.csr_idx     = inst_i[31:20];
        if (instr_type_i == i_slli || instr_type_i == i_srli || instr_type_i == i_srai) begin
          ctrl_o.imm_sel = I_USIMM;
        end else begin
          ctrl_o.imm_sel = I_IMM;
        end
        ctrl_o.alu_in2_sel  = 1'b1;
        ctrl_o.wr_en        = 1'b0;
        ctrl_o.result_src   = 2'b00;
        ctrl_o.rw_size      = NO_SIZE;
        ctrl_o.dcache_valid = 1'b0;
      end
      op_i_type_load: begin
        ctrl_o.rf_rw_en     = 1'b1;
        ctrl_o.csr_or_data  = 1'b0;
        ctrl_o.rd_csr       = 1'b0;
        ctrl_o.wr_csr       = 1'b0;
        ctrl_o.csr_idx      = inst_i[31:20];
        ctrl_o.imm_sel      = I_IMM;
        ctrl_o.alu_in2_sel  = 1'b1;
        ctrl_o.wr_en        = 1'b0;
        ctrl_o.result_src   = 2'b01;
        ctrl_o.dcache_valid = 1'b1;
        case (instr_type_i)
          i_lb, i_lbu: ctrl_o.rw_size = BYTE;
          i_lh, i_lhu: ctrl_o.rw_size = HALF;
          i_lw:        ctrl_o.rw_size = WORD;
          default:     ctrl_o.rw_size = NO_SIZE;
        endcase
      end
      op_s_type: begin
        ctrl_o.rf_rw_en     = 1'b0;
        ctrl_o.csr_or_data  = 1'b0;
        ctrl_o.rd_csr       = 1'b0;
        ctrl_o.wr_csr       = 1'b0;
        ctrl_o.csr_idx      = inst_i[31:20];
        ctrl_o.imm_sel      = S_IMM;
        ctrl_o.alu_in2_sel  = 1'b1;
        ctrl_o.wr_en        = 1'b1;
        ctrl_o.dcache_valid = 1'b1;
        case (instr_type_i)  // uniqeu case
          s_sb:    ctrl_o.rw_size = BYTE;
          s_sh:    ctrl_o.rw_size = HALF;
          s_sw:    ctrl_o.rw_size = WORD;
          default: ctrl_o.rw_size = NO_SIZE;
        endcase
        ctrl_o.result_src = 2'b00;
      end
      op_b_type: begin
        ctrl_o.rf_rw_en     = 1'b0;
        ctrl_o.csr_or_data  = 1'b0;
        ctrl_o.rd_csr       = 1'b0;
        ctrl_o.wr_csr       = 1'b0;
        ctrl_o.csr_idx      = inst_i[31:20];
        ctrl_o.imm_sel      = B_IMM;
        ctrl_o.alu_in2_sel  = 1'b0;
        ctrl_o.wr_en        = 1'b0;
        ctrl_o.result_src   = 2'b00;
        ctrl_o.rw_size      = NO_SIZE;
        ctrl_o.dcache_valid = 1'b0;
      end
      op_i_type_jump      : //i_jalr
        begin
        ctrl_o.rf_rw_en     = 1'b1;
        ctrl_o.csr_or_data  = 1'b0;
        ctrl_o.rd_csr       = 1'b0;
        ctrl_o.wr_csr       = 1'b0;
        ctrl_o.csr_idx      = inst_i[31:20];
        ctrl_o.imm_sel      = I_IMM;
        ctrl_o.alu_in2_sel  = 1'b1;
        ctrl_o.wr_en        = 1'b0;
        ctrl_o.result_src   = 2'b10;
        ctrl_o.rw_size      = NO_SIZE;
        ctrl_o.dcache_valid = 1'b0;
      end
      op_u_type_jump      : //u_jalr
        begin
        ctrl_o.rf_rw_en     = 1'b1;
        ctrl_o.csr_or_data  = 1'b0;
        ctrl_o.rd_csr       = 1'b0;
        ctrl_o.wr_csr       = 1'b0;
        ctrl_o.csr_idx      = inst_i[31:20];
        ctrl_o.imm_sel      = J_IMM;
        ctrl_o.alu_in2_sel  = 1'b0;
        ctrl_o.wr_en        = 1'b0;
        ctrl_o.result_src   = 2'b10;
        ctrl_o.rw_size      = NO_SIZE;
        ctrl_o.dcache_valid = 1'b0;
      end
      op_u_type_auipc: begin
        ctrl_o.rf_rw_en     = 1'b1;
        ctrl_o.csr_or_data  = 1'b0;
        ctrl_o.rd_csr       = 1'b0;
        ctrl_o.wr_csr       = 1'b0;
        ctrl_o.csr_idx      = inst_i[31:20];
        ctrl_o.imm_sel      = U_IMM;
        ctrl_o.alu_in2_sel  = 1'b1;
        ctrl_o.wr_en        = 1'b0;
        ctrl_o.result_src   = 2'b00;
        ctrl_o.rw_size      = NO_SIZE;
        ctrl_o.dcache_valid = 1'b0;
      end
      op_u_type_load: begin
        ctrl_o.rf_rw_en     = 1'b1;
        ctrl_o.csr_or_data  = 1'b0;
        ctrl_o.rd_csr       = 1'b0;
        ctrl_o.wr_csr       = 1'b0;
        ctrl_o.csr_idx      = inst_i[31:20];
        ctrl_o.imm_sel      = U_IMM;
        ctrl_o.alu_in2_sel  = 1'b1;
        ctrl_o.wr_en        = 1'b0;
        ctrl_o.result_src   = 2'b00;
        ctrl_o.rw_size      = NO_SIZE;
        ctrl_o.dcache_valid = 1'b0;
      end
      system: begin
        case (instr_type_i)

          CSR_RW: begin
            ctrl_o.rf_rw_en     = (inst_i.rd_addr != 0);
            ctrl_o.csr_or_data  = 1'b1;
            ctrl_o.rd_csr       = (inst_i.rd_addr != 0);  // CSR -> rd
            ctrl_o.wr_csr       = 1'b1;  // her zaman write
            ctrl_o.csr_idx      = inst_i[31:20];
            ctrl_o.imm_sel      = NO_IMM;
            ctrl_o.alu_in2_sel  = 1'b0;  // rs1
            ctrl_o.wr_en        = 1'b0;
            ctrl_o.result_src   = 2'b00;
            ctrl_o.rw_size      = NO_SIZE;
            ctrl_o.dcache_valid = 1'b0;
          end

          CSR_RS, CSR_RC: begin
            ctrl_o.rf_rw_en     = (inst_i.rd_addr != 0);
            ctrl_o.csr_or_data  = 1'b1;
            ctrl_o.rd_csr       = 1'b1;
            ctrl_o.wr_csr       = (inst_i.r1_addr != 0);  // rs1 != x0 ise write
            ctrl_o.csr_idx      = inst_i[31:20];
            ctrl_o.imm_sel      = NO_IMM;
            ctrl_o.alu_in2_sel  = 1'b0;  // rs1
            ctrl_o.wr_en        = 1'b0;
            ctrl_o.result_src   = 2'b00;
            ctrl_o.rw_size      = NO_SIZE;
            ctrl_o.dcache_valid = 1'b0;
          end

          CSR_RWI: begin
            ctrl_o.rf_rw_en     = (inst_i.rd_addr != 0);
            ctrl_o.csr_or_data  = 1'b1;
            ctrl_o.rd_csr       = (inst_i.rd_addr != 0);
            ctrl_o.wr_csr       = 1'b1;  // her zaman write
            ctrl_o.csr_idx      = inst_i[31:20];
            ctrl_o.imm_sel      = CSR_IMM;
            ctrl_o.alu_in2_sel  = 1'b1;  // zimm
            ctrl_o.wr_en        = 1'b0;
            ctrl_o.result_src   = 2'b00;
            ctrl_o.rw_size      = NO_SIZE;
            ctrl_o.dcache_valid = 1'b0;
          end

          CSR_RSI, CSR_RCI: begin
            ctrl_o.rf_rw_en     = (inst_i.rd_addr != 0);
            ctrl_o.csr_or_data  = 1'b1;
            ctrl_o.rd_csr       = 1'b1;
            ctrl_o.wr_csr       = (inst_i[19:15] != 5'd0);  // zimm != 0
            ctrl_o.csr_idx      = inst_i[31:20];
            ctrl_o.imm_sel      = CSR_IMM;
            ctrl_o.alu_in2_sel  = 1'b1;
            ctrl_o.wr_en        = 1'b0;
            ctrl_o.result_src   = 2'b00;
            ctrl_o.rw_size      = NO_SIZE;
            ctrl_o.dcache_valid = 1'b0;
          end
          mret, ecall, ebreak, wfi: begin
            ctrl_o.rf_rw_en     = 1'b0;
            ctrl_o.wr_csr       = 1'b0;
            ctrl_o.rd_csr       = 1'b0;
            ctrl_o.csr_idx      = 12'h000;  // CSR alanı geçersiz
            ctrl_o.csr_or_data  = 1'b0;
            ctrl_o.imm_sel      = NO_IMM;
            ctrl_o.alu_in2_sel  = 1'b0;
            ctrl_o.wr_en        = 1'b0;
            ctrl_o.result_src   = 2'b00;
            ctrl_o.rw_size      = NO_SIZE;
            ctrl_o.dcache_valid = 1'b0;
          end
          default: begin
            ctrl_o.rf_rw_en     = 1'b0;
            ctrl_o.wr_csr       = 1'b0;
            ctrl_o.rd_csr       = 1'b0;
            ctrl_o.csr_idx      = 12'h000;
            ctrl_o.csr_or_data  = 1'b0;
            ctrl_o.imm_sel      = NO_IMM;
            ctrl_o.alu_in2_sel  = 1'b0;
            ctrl_o.wr_en        = 1'b0;
            ctrl_o.result_src   = 2'b00;
            ctrl_o.rw_size      = NO_SIZE;
            ctrl_o.dcache_valid = 1'b0;
          end
        endcase
      end
      default: begin
        ctrl_o.rf_rw_en     = 1'b0;
        ctrl_o.csr_or_data  = 1'b0;
        ctrl_o.rd_csr       = 1'b0;
        ctrl_o.wr_csr       = 1'b0;
        ctrl_o.csr_idx      = inst_i[31:20];
        ctrl_o.imm_sel      = NO_IMM;
        ctrl_o.alu_in2_sel  = 1'b0;
        ctrl_o.wr_en        = 1'b0;
        ctrl_o.result_src   = 2'b00;
        ctrl_o.rw_size      = NO_SIZE;
        ctrl_o.dcache_valid = 1'b0;
      end
    endcase
  end

endmodule
