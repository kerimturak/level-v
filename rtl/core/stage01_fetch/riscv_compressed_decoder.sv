/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/

`timescale 1ns / 1ps

module riscv_compressed_decoder
  import ceres_param::*;
(
    input  logic [31:0] instr_i,
    output logic [31:0] instr_o,
    output logic        is_compressed_o,
    output logic        illegal_instr_o
);

  localparam OPCODE_SYSTEM = 7'h73;
  localparam OPCODE_FENCE = 7'h0f;
  localparam OPCODE_OP = 7'h33;
  localparam OPCODE_OPIMM = 7'h13;
  localparam OPCODE_STORE = 7'h23;
  localparam OPCODE_LOAD = 7'h03;
  localparam OPCODE_BRANCH = 7'h63;
  localparam OPCODE_JALR = 7'h67;
  localparam OPCODE_JAL = 7'h6f;
  localparam OPCODE_AUIPC = 7'h17;
  localparam OPCODE_LUI = 7'h37;
  localparam OPCODE_OP_FP = 7'h53;
  localparam OPCODE_OP_FMADD = 7'h43;
  localparam OPCODE_OP_FNMADD = 7'h4f;
  localparam OPCODE_OP_FMSUB = 7'h47;
  localparam OPCODE_OP_FNMSUB = 7'h4b;
  localparam OPCODE_STORE_FP = 7'h27;
  localparam OPCODE_LOAD_FP = 7'h07;
  localparam OPCODE_AMO = 7'h2F;
  generate

    always_comb begin
      illegal_instr_o = 1'b0;
      instr_o         = '0;

      case (instr_i[1:0])
        // C0
        2'b00: begin
          case (instr_i[15:13])
            3'b000: begin
              // c.addi4spn -> addi rd', x2, imm
              instr_o = {2'b0, instr_i[10:7], instr_i[12:11], instr_i[5], instr_i[6], 2'b00, 5'h02, 3'b000, 2'b01, instr_i[4:2], OPCODE_OPIMM};
              if (instr_i[12:5] == 8'b0) illegal_instr_o = 1'b1;
            end

            3'b010: begin
              // c.lw -> lw rd', imm(rs1')
              instr_o = {5'b0, instr_i[5], instr_i[12:10], instr_i[6], 2'b00, 2'b01, instr_i[9:7], 3'b010, 2'b01, instr_i[4:2], OPCODE_LOAD};
            end

            3'b110: begin
              // c.sw -> sw rs2', imm(rs1')
              instr_o = {5'b0, instr_i[5], instr_i[12], 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b010, instr_i[11:10], instr_i[6], 2'b00, OPCODE_STORE};
            end

            default: begin
              illegal_instr_o = 1'b1;
            end
          endcase
        end


        // C1
        2'b01: begin
          case (instr_i[15:13])
            3'b000: begin
              // c.addi -> addi rd, rd, nzimm
              // c.nop
              instr_o = {{6{instr_i[12]}}, instr_i[12], instr_i[6:2], instr_i[11:7], 3'b0, instr_i[11:7], OPCODE_OPIMM};
            end

            3'b001, 3'b101: begin
              // 001: c.jal -> jal x1, imm
              // 101: c.j   -> jal x0, imm
              instr_o = {instr_i[12], instr_i[8], instr_i[10:9], instr_i[6], instr_i[7], instr_i[2], instr_i[11], instr_i[5:3], {9{instr_i[12]}}, 4'b0, ~instr_i[15], OPCODE_JAL};
            end

            3'b010: begin
              // c.li -> addi rd, x0, nzimm
              instr_o = {{6{instr_i[12]}}, instr_i[12], instr_i[6:2], 5'b0, 3'b0, instr_i[11:7], OPCODE_OPIMM};
              if (instr_i[11:7] == 5'b0) illegal_instr_o = 1'b1;
            end

            3'b011: begin
              // c.lui -> lui rd, imm
              instr_o = {{15{instr_i[12]}}, instr_i[6:2], instr_i[11:7], OPCODE_LUI};

              if (instr_i[11:7] == 5'h02) begin
                // c.addi16sp -> addi x2, x2, nzimm
                instr_o = {{3{instr_i[12]}}, instr_i[4:3], instr_i[5], instr_i[2], instr_i[6], 4'b0, 5'h02, 3'b000, 5'h02, OPCODE_OPIMM};
              end else if (instr_i[11:7] == 5'b0) begin
                illegal_instr_o = 1'b1;
              end

              if ({instr_i[12], instr_i[6:2]} == 6'b0) illegal_instr_o = 1'b1;
            end

            3'b100: begin
              case (instr_i[11:10])
                2'b00, 2'b01: begin
                  // 00: c.srli -> srli rd, rd, shamt
                  // 01: c.srai -> srai rd, rd, shamt
                  instr_o = {1'b0, instr_i[10], 5'b0, instr_i[6:2], 2'b01, instr_i[9:7], 3'b101, 2'b01, instr_i[9:7], OPCODE_OPIMM};
                  if (instr_i[12] == 1'b1) illegal_instr_o = 1'b1;
                  if (instr_i[6:2] == 5'b0) illegal_instr_o = 1'b1;
                end

                2'b10: begin
                  // c.andi -> andi rd, rd, imm
                  instr_o = {{6{instr_i[12]}}, instr_i[12], instr_i[6:2], 2'b01, instr_i[9:7], 3'b111, 2'b01, instr_i[9:7], OPCODE_OPIMM};
                end

                2'b11: begin
                  case ({
                    instr_i[12], instr_i[6:5]
                  })
                    3'b000: begin
                      // c.sub -> sub rd', rd', rs2'
                      instr_o = {2'b01, 5'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b000, 2'b01, instr_i[9:7], OPCODE_OP};
                    end

                    3'b001: begin
                      // c.xor -> xor rd', rd', rs2'
                      instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b100, 2'b01, instr_i[9:7], OPCODE_OP};
                    end

                    3'b010: begin
                      // c.or  -> or  rd', rd', rs2'
                      instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b110, 2'b01, instr_i[9:7], OPCODE_OP};
                    end

                    3'b011: begin
                      // c.and -> and rd', rd', rs2'
                      instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b111, 2'b01, instr_i[9:7], OPCODE_OP};
                    end

                    3'b100, 3'b101, 3'b110, 3'b111: begin
                      // 100: c.subw
                      // 101: c.addw
                      illegal_instr_o = 1'b1;
                    end
                  endcase
                end
              endcase
            end

            3'b110, 3'b111: begin
              // 0: c.beqz -> beq rs1', x0, imm
              // 1: c.bnez -> bne rs1', x0, imm
              instr_o = {{4{instr_i[12]}}, instr_i[6:5], instr_i[2], 5'b0, 2'b01, instr_i[9:7], 2'b00, instr_i[13], instr_i[11:10], instr_i[4:3], instr_i[12], OPCODE_BRANCH};
            end
          endcase
        end

        // C2
        2'b10: begin
          case (instr_i[15:13])
            3'b000: begin
              // c.slli -> slli rd, rd, shamt
              instr_o = {7'b0, instr_i[6:2], instr_i[11:7], 3'b001, instr_i[11:7], OPCODE_OPIMM};
              if (instr_i[11:7] == 5'b0) illegal_instr_o = 1'b1;
              if (instr_i[12] == 1'b1 || instr_i[6:2] == 5'b0) illegal_instr_o = 1'b1;
            end

            3'b010: begin
              // c.lwsp -> lw rd, imm(x2)
              instr_o = {4'b0, instr_i[3:2], instr_i[12], instr_i[6:4], 2'b00, 5'h02, 3'b010, instr_i[11:7], OPCODE_LOAD};
              if (instr_i[11:7] == 5'b0) illegal_instr_o = 1'b1;
            end

            3'b100: begin
              if (instr_i[12] == 1'b0) begin
                // c.mv -> add rd/rs1, x0, rs2
                instr_o = {7'b0, instr_i[6:2], 5'b0, 3'b0, instr_i[11:7], OPCODE_OP};

                if (instr_i[6:2] == 5'b0) begin
                  // c.jr -> jalr x0, rd/rs1, 0
                  instr_o = {12'b0, instr_i[11:7], 3'b0, 5'b0, OPCODE_JALR};
                end
                // Note: c.mv with rd=x0 is a HINT, not illegal
              end else begin
                // c.add -> add rd, rd, rs2
                instr_o = {7'b0, instr_i[6:2], instr_i[11:7], 3'b0, instr_i[11:7], OPCODE_OP};

                if (instr_i[11:7] == 5'b0 && instr_i[6:2] == 5'b0) begin
                  // c.ebreak -> ebreak (rd=0, rs2=0)
                  instr_o = {32'h00_10_00_73};
                end else if (instr_i[11:7] == 5'b0) begin
                  // c.add x0, rs2 is a HINT (rd=0, rs2!=0) - treat as NOP
                  instr_o = {25'b0, OPCODE_OP};  // add x0, x0, x0 = NOP
                end else if (instr_i[6:2] == 5'b0) begin
                  // c.jalr -> jalr x1, rs1, 0
                  instr_o = {12'b0, instr_i[11:7], 3'b000, 5'b00001, OPCODE_JALR};
                end
              end
            end

            3'b110: begin
              // c.swsp -> sw rs2, imm(x2)
              instr_o = {4'b0, instr_i[8:7], instr_i[12], instr_i[6:2], 5'h02, 3'b010, instr_i[11:9], 2'b00, OPCODE_STORE};
            end

          endcase
        end

        default: begin
          // 32 bit (or more) instruction
          instr_o = instr_i;
        end
      endcase
    end

  endgenerate

  assign is_compressed_o = (instr_i[1:0] != 2'b11);

endmodule
