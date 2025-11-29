/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/

`timescale 1ns / 1ps

module compressed_decoder
  import ceres_param::*;
(
    input  logic [31:0] instr_i,
    output logic [31:0] instr_o,
    output logic        is_compressed_o,
    output logic        illegal_instr_o
);

  // ============================================================================
  // Opcode Definitions (RV32I Base)
  // ============================================================================
  localparam logic [6:0] OPCODE_LOAD = 7'h03;
  localparam logic [6:0] OPCODE_STORE = 7'h23;
  localparam logic [6:0] OPCODE_BRANCH = 7'h63;
  localparam logic [6:0] OPCODE_JALR = 7'h67;
  localparam logic [6:0] OPCODE_JAL = 7'h6f;
  localparam logic [6:0] OPCODE_OPIMM = 7'h13;
  localparam logic [6:0] OPCODE_OP = 7'h33;
  localparam logic [6:0] OPCODE_LUI = 7'h37;
  localparam logic [6:0] OPCODE_SYSTEM = 7'h73;

  // Funct3 definitions for clarity
  localparam logic [2:0] FUNCT3_ADD = 3'b000;
  localparam logic [2:0] FUNCT3_SLL = 3'b001;
  localparam logic [2:0] FUNCT3_LW = 3'b010;
  localparam logic [2:0] FUNCT3_SW = 3'b010;
  localparam logic [2:0] FUNCT3_XOR = 3'b100;
  localparam logic [2:0] FUNCT3_SRL = 3'b101;
  localparam logic [2:0] FUNCT3_OR = 3'b110;
  localparam logic [2:0] FUNCT3_AND = 3'b111;
  localparam logic [2:0] FUNCT3_BEQ = 3'b000;
  localparam logic [2:0] FUNCT3_BNE = 3'b001;

  // Funct7 definitions
  localparam logic [6:0] FUNCT7_ZERO = 7'b0000000;
  localparam logic [6:0] FUNCT7_SUB = 7'b0100000;  // SUB, SRA

  // Special register addresses
  localparam logic [4:0] REG_ZERO = 5'h00;  // x0
  localparam logic [4:0] REG_RA = 5'h01;  // x1 - return address
  localparam logic [4:0] REG_SP = 5'h02;  // x2 - stack pointer

  // ============================================================================
  // Instruction Field Extraction
  // ============================================================================

  // Quadrant and funct3 fields
  logic [1:0] quadrant;
  logic [2:0] funct3;

  assign quadrant = instr_i[1:0];
  assign funct3   = instr_i[15:13];

  // Full register addresses (5-bit) - for C2 quadrant
  logic [4:0] rd_rs1_full;  // rd/rs1 field [11:7]
  logic [4:0] rs2_full;  // rs2 field [6:2]

  assign rd_rs1_full = instr_i[11:7];
  assign rs2_full    = instr_i[6:2];

  // Compressed register addresses (3-bit -> 5-bit) - for C0/C1 quadrant
  // Registers x8-x15 are encoded as 0-7
  logic [4:0] rd_prime;  // rd' = 8 + instr_i[4:2]
  logic [4:0] rs1_prime;  // rs1' = 8 + instr_i[9:7]
  logic [4:0] rs2_prime;  // rs2' = 8 + instr_i[4:2]

  assign rd_prime  = {2'b01, instr_i[4:2]};
  assign rs1_prime = {2'b01, instr_i[9:7]};
  assign rs2_prime = {2'b01, instr_i[4:2]};

  // ============================================================================
  // Immediate Value Extraction Functions
  // ============================================================================

  // C.ADDI4SPN immediate: nzuimm[5:4|9:6|2|3] scaled by 4
  function automatic logic [11:0] get_imm_addi4spn();
    return {2'b0, instr_i[10:7], instr_i[12:11], instr_i[5], instr_i[6], 2'b00};
  endfunction

  // C.LW/C.SW immediate: uimm[5:3|2|6] scaled by 4
  function automatic logic [11:0] get_imm_lw_sw();
    return {5'b0, instr_i[5], instr_i[12:10], instr_i[6], 2'b00};
  endfunction

  // C.ADDI/C.LI immediate: nzimm[5] | imm[4:0] sign-extended
  function automatic logic [11:0] get_imm_ci();
    return {{6{instr_i[12]}}, instr_i[12], instr_i[6:2]};
  endfunction

  // C.LUI immediate: nzimm[17] | imm[16:12] sign-extended to upper 20 bits
  function automatic logic [19:0] get_imm_lui();
    return {{14{instr_i[12]}}, instr_i[12], instr_i[6:2]};
  endfunction

  // C.ADDI16SP immediate: nzimm[9] | imm[4|6|8:7|5] scaled by 16
  function automatic logic [11:0] get_imm_addi16sp();
    return {{3{instr_i[12]}}, instr_i[4:3], instr_i[5], instr_i[2], instr_i[6], 4'b0};
  endfunction

  // C.J/C.JAL: Generate the 32-bit JAL instruction directly
  // Compressed immediate fields map to JAL's imm[20|10:1|11|19:12] format
  function automatic logic [31:0] gen_c_jal(input logic [4:0] rd);
    // offset[11|4|9:8|10|6|7|3:1|5] from compressed instruction
    // maps directly to JAL format: imm[20|10:1|11|19:12]
    return {instr_i[12], instr_i[8], instr_i[10:9], instr_i[6], instr_i[7], instr_i[2], instr_i[11], instr_i[5:3], {9{instr_i[12]}}, rd, OPCODE_JAL};
  endfunction

  // C.BEQZ/C.BNEZ: Generate the 32-bit Branch instruction directly
  // offset[8|4:3|7:6|2:1|5] from compressed instruction
  function automatic logic [31:0] gen_c_branch(input logic [2:0] f3);
    return {{4{instr_i[12]}}, instr_i[6:5], instr_i[2], REG_ZERO, rs1_prime, f3, instr_i[11:10], instr_i[4:3], instr_i[12], OPCODE_BRANCH};
  endfunction

  // C.LWSP immediate: uimm[5] | imm[4:2|7:6] scaled by 4
  function automatic logic [11:0] get_imm_lwsp();
    return {4'b0, instr_i[3:2], instr_i[12], instr_i[6:4], 2'b00};
  endfunction

  // C.SWSP immediate: uimm[5:2|7:6] scaled by 4
  function automatic logic [11:0] get_imm_swsp();
    return {4'b0, instr_i[8:7], instr_i[12:9], 2'b00};
  endfunction

  // Shift amount (5-bit)
  function automatic logic [4:0] get_shamt();
    return instr_i[6:2];
  endfunction

  // ============================================================================
  // Instruction Generation Functions
  // ============================================================================

  // R-type: funct7[6:0] | rs2[4:0] | rs1[4:0] | funct3[2:0] | rd[4:0] | opcode[6:0]
  function automatic logic [31:0] gen_r_type(input logic [6:0] funct7, input logic [4:0] rs2, input logic [4:0] rs1, input logic [2:0] f3, input logic [4:0] rd, input logic [6:0] opcode);
    return {funct7, rs2, rs1, f3, rd, opcode};
  endfunction

  // I-type: imm[11:0] | rs1[4:0] | funct3[2:0] | rd[4:0] | opcode[6:0]
  function automatic logic [31:0] gen_i_type(input logic [11:0] imm, input logic [4:0] rs1, input logic [2:0] f3, input logic [4:0] rd, input logic [6:0] opcode);
    return {imm, rs1, f3, rd, opcode};
  endfunction

  // S-type: imm[11:5] | rs2[4:0] | rs1[4:0] | funct3[2:0] | imm[4:0] | opcode[6:0]
  function automatic logic [31:0] gen_s_type(input logic [11:0] imm, input logic [4:0] rs2, input logic [4:0] rs1, input logic [2:0] f3, input logic [6:0] opcode);
    return {imm[11:5], rs2, rs1, f3, imm[4:0], opcode};
  endfunction

  // U-type: imm[31:12] | rd[4:0] | opcode[6:0]
  function automatic logic [31:0] gen_u_type(input logic [19:0] imm, input logic [4:0] rd, input logic [6:0] opcode);
    return {imm, rd, opcode};
  endfunction

  // ============================================================================
  // Quadrant Decode Results
  // ============================================================================

  logic [31:0] c0_instr, c1_instr, c2_instr;
  logic c0_illegal, c1_illegal, c2_illegal;

  // ============================================================================
  // C0 Quadrant Decoder (opcode = 2'b00)
  // ============================================================================
  always_comb begin
    c0_instr   = '0;
    c0_illegal = 1'b0;

    case (funct3)
      3'b000: begin
        // C.ADDI4SPN: addi rd', x2, nzuimm
        c0_instr = gen_i_type(get_imm_addi4spn(), REG_SP, FUNCT3_ADD, rd_prime, OPCODE_OPIMM);
        if (instr_i[12:5] == 8'b0) c0_illegal = 1'b1;  // nzuimm == 0 is reserved
      end

      3'b010: begin
        // C.LW: lw rd', offset(rs1')
        c0_instr = gen_i_type(get_imm_lw_sw(), rs1_prime, FUNCT3_LW, rd_prime, OPCODE_LOAD);
      end

      3'b110: begin
        // C.SW: sw rs2', offset(rs1')
        c0_instr = gen_s_type(get_imm_lw_sw(), rs2_prime, rs1_prime, FUNCT3_SW, OPCODE_STORE);
      end

      default: begin
        c0_illegal = 1'b1;
      end
    endcase
  end

  // ============================================================================
  // C1 Quadrant Decoder (opcode = 2'b01)
  // ============================================================================
  always_comb begin
    c1_instr   = '0;
    c1_illegal = 1'b0;

    case (funct3)
      3'b000: begin
        // C.ADDI / C.NOP: addi rd, rd, nzimm
        c1_instr = gen_i_type(get_imm_ci(), rd_rs1_full, FUNCT3_ADD, rd_rs1_full, OPCODE_OPIMM);
        // Note: rd=x0 is C.NOP (valid), nzimm=0 with rd!=0 is HINT (valid)
      end

      3'b001: begin
        // C.JAL: jal x1, offset (RV32C only)
        c1_instr = gen_c_jal(REG_RA);
      end

      3'b101: begin
        // C.J: jal x0, offset
        c1_instr = gen_c_jal(REG_ZERO);
      end

      3'b010: begin
        // C.LI: addi rd, x0, imm
        // Note: rd=x0 is HINT (valid, treated as NOP)
        c1_instr = gen_i_type(get_imm_ci(), REG_ZERO, FUNCT3_ADD, rd_rs1_full, OPCODE_OPIMM);
      end

      3'b011: begin
        if (rd_rs1_full == REG_SP) begin
          // C.ADDI16SP: addi x2, x2, nzimm
          c1_instr = gen_i_type(get_imm_addi16sp(), REG_SP, FUNCT3_ADD, REG_SP, OPCODE_OPIMM);
        end else begin
          // C.LUI: lui rd, nzimm
          // Note: rd=x0 is HINT (valid, treated as NOP)
          c1_instr = gen_u_type(get_imm_lui(), rd_rs1_full, OPCODE_LUI);
        end
        // Check for reserved encodings
        // Note: rd=x0 case goes to C.LUI which is HINT, not illegal
        // But nzimm=0 is reserved for both C.ADDI16SP and C.LUI
        if ({instr_i[12], instr_i[6:2]} == 6'b0) c1_illegal = 1'b1;  // nzimm=0 is reserved
      end

      3'b100: begin
        // C.SRLI, C.SRAI, C.ANDI, C.SUB, C.XOR, C.OR, C.AND
        case (instr_i[11:10])
          2'b00: begin
            // C.SRLI: srli rd', rd', shamt
            c1_instr = gen_i_type({7'b0, get_shamt()}, rs1_prime, FUNCT3_SRL, rs1_prime, OPCODE_OPIMM);
            if (instr_i[12]) c1_illegal = 1'b1;  // shamt[5] must be 0 for RV32
            if (get_shamt() == 5'b0) c1_illegal = 1'b1;  // shamt=0 is reserved
          end

          2'b01: begin
            // C.SRAI: srai rd', rd', shamt
            c1_instr = gen_i_type({FUNCT7_SUB, get_shamt()}, rs1_prime, FUNCT3_SRL, rs1_prime, OPCODE_OPIMM);
            if (instr_i[12]) c1_illegal = 1'b1;  // shamt[5] must be 0 for RV32
            if (get_shamt() == 5'b0) c1_illegal = 1'b1;  // shamt=0 is reserved
          end

          2'b10: begin
            // C.ANDI: andi rd', rd', imm
            c1_instr = gen_i_type(get_imm_ci(), rs1_prime, FUNCT3_AND, rs1_prime, OPCODE_OPIMM);
          end

          2'b11: begin
            // Register-register operations
            case ({
              instr_i[12], instr_i[6:5]
            })
              3'b000: begin
                // C.SUB: sub rd', rd', rs2'
                c1_instr = gen_r_type(FUNCT7_SUB, rs2_prime, rs1_prime, FUNCT3_ADD, rs1_prime, OPCODE_OP);
              end
              3'b001: begin
                // C.XOR: xor rd', rd', rs2'
                c1_instr = gen_r_type(FUNCT7_ZERO, rs2_prime, rs1_prime, FUNCT3_XOR, rs1_prime, OPCODE_OP);
              end
              3'b010: begin
                // C.OR: or rd', rd', rs2'
                c1_instr = gen_r_type(FUNCT7_ZERO, rs2_prime, rs1_prime, FUNCT3_OR, rs1_prime, OPCODE_OP);
              end
              3'b011: begin
                // C.AND: and rd', rd', rs2'
                c1_instr = gen_r_type(FUNCT7_ZERO, rs2_prime, rs1_prime, FUNCT3_AND, rs1_prime, OPCODE_OP);
              end
              default: begin
                // C.SUBW, C.ADDW (RV64C only) - illegal in RV32
                c1_illegal = 1'b1;
              end
            endcase
          end
        endcase
      end

      3'b110: begin
        // C.BEQZ: beq rs1', x0, offset
        c1_instr = gen_c_branch(FUNCT3_BEQ);
      end

      3'b111: begin
        // C.BNEZ: bne rs1', x0, offset
        c1_instr = gen_c_branch(FUNCT3_BNE);
      end
    endcase
  end

  // ============================================================================
  // C2 Quadrant Decoder (opcode = 2'b10)
  // ============================================================================
  always_comb begin
    c2_instr   = '0;
    c2_illegal = 1'b0;

    case (funct3)
      3'b000: begin
        // C.SLLI: slli rd, rd, shamt
        // Note: rd=x0 is HINT (valid, treated as NOP)
        c2_instr = gen_i_type({7'b0, get_shamt()}, rd_rs1_full, FUNCT3_SLL, rd_rs1_full, OPCODE_OPIMM);
        if (instr_i[12] || get_shamt() == 5'b0) c2_illegal = 1'b1;  // shamt[5]=1 or shamt=0 is reserved
      end

      3'b010: begin
        // C.LWSP: lw rd, offset(x2)
        c2_instr = gen_i_type(get_imm_lwsp(), REG_SP, FUNCT3_LW, rd_rs1_full, OPCODE_LOAD);
        if (rd_rs1_full == REG_ZERO) c2_illegal = 1'b1;  // rd=x0 is reserved
      end

      3'b100: begin
        if (!instr_i[12]) begin
          // C.MV or C.JR
          if (rs2_full == REG_ZERO) begin
            // C.JR: jalr x0, rs1, 0
            c2_instr = gen_i_type(12'b0, rd_rs1_full, FUNCT3_ADD, REG_ZERO, OPCODE_JALR);
            if (rd_rs1_full == REG_ZERO) c2_illegal = 1'b1;  // rs1=x0 is reserved
          end else begin
            // C.MV: add rd, x0, rs2
            c2_instr = gen_r_type(FUNCT7_ZERO, rs2_full, REG_ZERO, FUNCT3_ADD, rd_rs1_full, OPCODE_OP);
            // Note: rd=x0 is HINT (valid)
          end
        end else begin
          // C.ADD, C.JALR, or C.EBREAK
          if (rd_rs1_full == REG_ZERO && rs2_full == REG_ZERO) begin
            // C.EBREAK: ebreak
            c2_instr = 32'h00100073;
          end else if (rs2_full == REG_ZERO) begin
            // C.JALR: jalr x1, rs1, 0
            c2_instr = gen_i_type(12'b0, rd_rs1_full, FUNCT3_ADD, REG_RA, OPCODE_JALR);
          end else if (rd_rs1_full == REG_ZERO) begin
            // C.ADD with rd=x0 is HINT, treat as NOP
            c2_instr = gen_r_type(FUNCT7_ZERO, REG_ZERO, REG_ZERO, FUNCT3_ADD, REG_ZERO, OPCODE_OP);
          end else begin
            // C.ADD: add rd, rd, rs2
            c2_instr = gen_r_type(FUNCT7_ZERO, rs2_full, rd_rs1_full, FUNCT3_ADD, rd_rs1_full, OPCODE_OP);
          end
        end
      end

      3'b110: begin
        // C.SWSP: sw rs2, offset(x2)
        c2_instr = gen_s_type(get_imm_swsp(), rs2_full, REG_SP, FUNCT3_SW, OPCODE_STORE);
      end

      default: begin
        c2_illegal = 1'b1;
      end
    endcase
  end

  // ============================================================================
  // Output Multiplexer
  // ============================================================================
  always_comb begin
    case (quadrant)
      2'b00: begin
        instr_o         = c0_instr;
        illegal_instr_o = c0_illegal;
      end
      2'b01: begin
        instr_o         = c1_instr;
        illegal_instr_o = c1_illegal;
      end
      2'b10: begin
        instr_o         = c2_instr;
        illegal_instr_o = c2_illegal;
      end
      default: begin
        // Non-compressed instruction (32-bit or wider)
        instr_o         = instr_i;
        illegal_instr_o = 1'b0;
      end
    endcase
  end

  // ============================================================================
  // Compressed Instruction Detection
  // ============================================================================
  assign is_compressed_o = (quadrant != 2'b11);

endmodule
