/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
`include "ceres_defines.svh"
package ceres_param;
  localparam CPU_CLK = 50_000_000;
  localparam PROG_BAUD_RATE = 115200;
  localparam PROGRAM_SEQUENCE = "CERESTEST";

  localparam RESET_VECTOR = 32'h8000_0000;
  localparam RAS_SIZE = 8;
  localparam XLEN = 32;
  localparam BLK_SIZE = 128;

  localparam [6:0] system = 7'b11100_11;
  localparam [6:0] op_fence_i = 7'b00011_11;
  localparam [6:0] op_r_type = 7'b01100_11;  // 51, add, sub, sll, slt, sltu, xor, srl, sra, or, and,
  localparam [6:0] op_i_type_load = 7'b00000_11;  // lb, lh, lw, lbu, lhu,
  localparam [6:0] op_i_type = 7'b00100_11;  // addi, slti, sltiu, xori, ori, andi, slli, srli, srai,
  localparam [6:0] op_s_type = 7'b01000_11;  // sb, sh, sw,
  localparam [6:0] op_b_type = 7'b11000_11;  // beq, bne, blt, bge, bltu, bgeu,
  localparam [6:0] op_i_type_jump = 7'b11001_11;  // jal
  localparam [6:0] op_u_type_load = 7'b01101_11;  // u type load
  localparam [6:0] op_u_type_jump = 7'b11011_11;
  localparam [6:0] op_u_type_auipc = 7'b00101_11;


  localparam IC_WAY = 8;
  localparam DC_WAY = 8;
  localparam IC_CAPACITY = 32 * (2 ** 10) * 8;
  localparam DC_CAPACITY = 32 * (2 ** 10) * 8;

  localparam Mul_Type = 0;  // 1: dadda 0: wallace

  typedef struct packed {
    logic [XLEN-1:0] pc;
    logic [XLEN-1:0] inst;
    logic [63:0]     sn;    // ← Konata ID (serial number)
  } fe_tracer_info_t;


  typedef struct packed {
    logic            valid;
    logic [XLEN-1:0] data;
  } ras_t;

  typedef enum logic [1:0] {
    NO_SPEC,
    RAS,
    JUMP,
    BRANCH
  } spec_type_e;

  typedef enum logic [2:0] {
    NO_STALL = 0,
    LOAD_RAW_STALL = 1,
    IMISS_STALL = 2,
    DMISS_STALL = 3,
    ALU_STALL = 4,
    FENCEI_STALL = 5
  } stall_e;

  typedef enum logic [5:0] {
    Null_Instr_Type,
    instr_invalid,
    r_add,
    r_sub,
    r_sll,
    r_slt,
    r_sltu,
    r_xor,
    r_srl,
    r_sra,
    r_or,
    r_and,
    i_addi,
    i_slti,
    i_sltiu,
    i_xori,
    i_ori,
    i_andi,
    i_slli,
    i_srli,
    i_srai,
    r_mul,
    r_mulh,
    r_mulhsu,
    r_mulhu,
    r_rem,
    r_remu,
    r_div,
    r_divu,
    i_lb,
    i_lh,
    i_lw,
    i_lbu,
    i_lhu,
    s_sb,
    s_sh,
    s_sw,
    b_beq,
    b_bne,
    b_blt,
    b_bge,
    b_bltu,
    b_bgeu,
    u_lui,
    u_auipc,
    u_jal,
    i_jalr,
    CSR_RW,
    CSR_RS,
    CSR_RC,
    CSR_RWI,
    CSR_RSI,
    CSR_RCI,
    ecall,
    ebreak,
    mret,
    wfi,
    fence_i,
    fence
  } instr_type_e;

  typedef struct packed {
    logic [6:0] funct7;
    logic [4:0] r2_addr;
    logic [4:0] r1_addr;
    logic [2:0] funct3;
    logic [4:0] rd_addr;
    logic [6:0] opcode;
  } inst_t;

  function instr_type_e resolved_instr_type;
    input inst_t inst_i;

    case (inst_i.opcode)
      op_fence_i: begin
        if (inst_i.funct3 == '0) begin
          resolved_instr_type = fence;
        end else if (inst_i.funct3 == 3'b001) begin
          resolved_instr_type = fence_i;
        end else begin
          resolved_instr_type = instr_invalid;
        end
      end
      op_r_type: begin
        if (inst_i.funct7[0]) begin
          case (inst_i.funct3)
            3'd0:    resolved_instr_type = r_mul;
            3'd1:    resolved_instr_type = r_mulh;
            3'd2:    resolved_instr_type = r_mulhsu;
            3'd3:    resolved_instr_type = r_mulhu;
            3'd4:    resolved_instr_type = r_div;
            3'd5:    resolved_instr_type = r_divu;
            3'd6:    resolved_instr_type = r_rem;
            3'd7:    resolved_instr_type = r_remu;
            default: resolved_instr_type = instr_invalid;
          endcase
        end else begin
          case (inst_i.funct3)
            3'd0:    resolved_instr_type = (inst_i.funct7[5] == 1'b0) ? r_add : r_sub;
            3'd1:    resolved_instr_type = r_sll;
            3'd2:    resolved_instr_type = r_slt;
            3'd3:    resolved_instr_type = r_sltu;
            3'd4:    resolved_instr_type = r_xor;
            3'd5:    resolved_instr_type = (inst_i.funct7[5] == 1'b0) ? r_srl : r_sra;
            3'd6:    resolved_instr_type = r_or;
            3'd7:    resolved_instr_type = r_and;
            default: resolved_instr_type = instr_invalid;
          endcase
        end

      end

      op_i_type_load: begin
        case (inst_i.funct3)
          3'd0:    resolved_instr_type = i_lb;
          3'd1:    resolved_instr_type = i_lh;
          3'd2:    resolved_instr_type = i_lw;
          3'd4:    resolved_instr_type = i_lbu;
          3'd5:    resolved_instr_type = i_lhu;
          default: resolved_instr_type = instr_invalid;
        endcase
      end

      op_i_type: begin
        case (inst_i.funct3)
          3'd0:    resolved_instr_type = i_addi;
          3'd2:    resolved_instr_type = i_slti;
          3'd3:    resolved_instr_type = i_sltiu;
          3'd4:    resolved_instr_type = i_xori;
          3'd6:    resolved_instr_type = i_ori;
          3'd7:    resolved_instr_type = i_andi;
          3'd1:    resolved_instr_type = i_slli;
          3'd5:    resolved_instr_type = (inst_i.funct7[5] == 1'b0) ? i_srli : i_srai;
          default: resolved_instr_type = instr_invalid;
        endcase
      end

      op_s_type: begin
        case (inst_i.funct3)
          3'd0:    resolved_instr_type = s_sb;
          3'd1:    resolved_instr_type = s_sh;
          3'd2:    resolved_instr_type = s_sw;
          default: resolved_instr_type = instr_invalid;
        endcase
      end

      op_b_type: begin
        case (inst_i.funct3)
          3'd0:    resolved_instr_type = b_beq;
          3'd1:    resolved_instr_type = b_bne;
          3'd4:    resolved_instr_type = b_blt;
          3'd5:    resolved_instr_type = b_bge;
          3'd6:    resolved_instr_type = b_bltu;
          3'd7:    resolved_instr_type = b_bgeu;
          default: resolved_instr_type = instr_invalid;
        endcase
      end

      op_u_type_load:  resolved_instr_type = u_lui;
      op_u_type_auipc: resolved_instr_type = u_auipc;
      op_u_type_jump:  resolved_instr_type = u_jal;
      op_i_type_jump:  resolved_instr_type = i_jalr;

      system: begin
        case (inst_i.funct3)
          3'd1:    resolved_instr_type = CSR_RW;
          3'd2:    resolved_instr_type = CSR_RS;
          3'd3:    resolved_instr_type = CSR_RC;
          3'd5:    resolved_instr_type = CSR_RWI;
          3'd6:    resolved_instr_type = CSR_RSI;
          3'd7:    resolved_instr_type = CSR_RCI;
          3'd0: begin
            case (inst_i[31:20])
              12'h000: resolved_instr_type = ecall;
              12'h001: resolved_instr_type = ebreak;
              12'h302: resolved_instr_type = mret;
              default: resolved_instr_type = instr_invalid;
            endcase
          end
          default: resolved_instr_type = instr_invalid;
        endcase
      end

      default: resolved_instr_type = instr_invalid;  // Geçersiz talimat
    endcase
    return resolved_instr_type;
  endfunction

  typedef enum logic [3:0] {
    INSTR_MISALIGNED,
    INSTR_ACCESS_FAULT,
    ILLEGAL_INSTRUCTION,
    EBREAK,
    LOAD_MISALIGNED,
    LOAD_ACCESS_FAULT,
    STORE_MISALIGNED,
    STORE_ACCESS_FAULT,
    ECALL,
    NO_EXCEPTION
  } exc_type_e;

  typedef enum logic [2:0] {
    CSRRW  = 3'h1,
    CSRRS  = 3'h2,
    CSRRC  = 3'h3,
    CSRRWI = 3'h5,
    CSRRSI = 3'h6,
    CSRRCI = 3'h7
  } csr_op_t;

  typedef enum logic [3:0] {
    NO_BJ,
    BEQ,
    BNE,
    BLT,
    BGE,
    BLTU,
    BGEU,
    JALR,
    JAL
  } pc_sel_e;

  typedef enum logic [3:0] {
    NO_IMM,
    I_IMM,
    I_USIMM,
    S_IMM,
    B_IMM,
    U_IMM,
    J_IMM,
    CSR_IMM
  } imm_e;

  typedef enum logic [4:0] {
    OP_ADD,
    OP_SUB,
    OP_SLL,
    OP_SLT,
    OP_SLTU,
    OP_XOR,
    OP_SRL,
    OP_SRA,
    OP_OR,
    OP_AND,
    OP_MUL,
    OP_MULH,
    OP_MULHSU,
    OP_MULHU,
    OP_DIV,
    OP_DIVU,
    OP_REM,
    OP_REMU,
    OP_LUI,
    OP_CSRRW,
    OP_CSRRS,
    OP_CSRRC,
    OP_CSRRWI,
    OP_CSRRSI,
    OP_CSRRCI
  } alu_op_e;

  typedef struct packed {
    logic            taken;
    logic [XLEN-1:0] pc;
    spec_type_e      spectype;
  } predict_info_t;

  function pc_sel_e is_branch(instr_type_e instr);
    case (instr)
      b_beq:   return BEQ;
      b_bne:   return BNE;
      b_blt:   return BLT;
      b_bge:   return BGE;
      b_bltu:  return BLTU;
      b_bgeu:  return BGEU;
      i_jalr:  return JALR;
      u_jal:   return JAL;
      default: return NO_BJ;
    endcase
  endfunction

  typedef struct packed {
    logic [XLEN-1:0] pc;
    logic [XLEN-1:0] pc_incr;
    inst_t           inst;
    exc_type_e       exc_type;
    instr_type_e     instr_type;
    predict_info_t   spec;
`ifdef COMMIT_TRACER
    fe_tracer_info_t fe_tracer;
`endif
  } pipe1_t;

  typedef struct packed {
    exc_type_e       exc_type;
    predict_info_t   spec;
    pc_sel_e         bjtype;
    logic [XLEN-1:0] pc;
  } pipe_info_t;

  typedef struct packed {
    logic [XLEN-1:0] pc;
    logic [XLEN-1:0] pc_incr;
    logic            rf_rw_en;
    logic            wr_en;
    logic [1:0]      rw_size;
    logic [1:0]      result_src;
    alu_op_e         alu_ctrl;
    pc_sel_e         pc_sel;
    logic [1:0]      alu_in1_sel;
    logic            alu_in2_sel;
    logic            ld_op_sign;
    logic [XLEN-1:0] r1_data;
    logic [XLEN-1:0] r2_data;
    logic [4:0]      r1_addr;
    logic [4:0]      r2_addr;
    logic [4:0]      rd_addr;       //! destination register address
    logic [XLEN-1:0] imm;           //! immediate generater output
    logic            rd_csr;
    logic            wr_csr;
    logic [11:0]     csr_idx;
    logic            csr_or_data;
    instr_type_e     instr_type;
    predict_info_t   spec;
    logic            dcache_valid;
`ifdef COMMIT_TRACER
    fe_tracer_info_t fe_tracer;
`endif
  } pipe2_t;

  typedef struct packed {
    logic [XLEN-1:0] pc_incr;
    logic [XLEN-1:0] pc;
    logic            rf_rw_en;
    logic            wr_en;
    logic [1:0]      rw_size;
    logic [1:0]      result_src;
    logic            ld_op_sign;
    logic [4:0]      rd_addr;
    logic [XLEN-1:0] alu_result;
    logic [XLEN-1:0] write_data;
    logic            dcache_valid;
    logic [XLEN-1:0] read_data;
`ifdef COMMIT_TRACER
    fe_tracer_info_t fe_tracer;
    logic            rd_en_csr;
    logic            wr_en_csr;
    logic [11:0]     csr_idx;
    instr_type_e     instr_type;
    logic [XLEN-1:0] csr_wr_data;
`endif
  } pipe3_t;

  typedef struct packed {
    logic [XLEN-1:0] pc_incr;
    logic [XLEN-1:0] pc;
    logic            rf_rw_en;
    logic [1:0]      result_src;
    logic [4:0]      rd_addr;
    logic [XLEN-1:0] alu_result;
    logic [XLEN-1:0] read_data;
`ifdef COMMIT_TRACER
    fe_tracer_info_t fe_tracer;
    logic            wr_en;
    logic [1:0]      rw_size;
    logic [XLEN-1:0] write_data;
    logic            rd_en_csr;
    logic            wr_en_csr;
    logic [11:0]     csr_idx;
    instr_type_e     instr_type;
    logic [XLEN-1:0] csr_wr_data;
    logic            dcache_valid;
`endif
  } pipe4_t;

  typedef struct packed {
    logic        rf_rw_en;
    imm_e        imm_sel;
    logic        wr_en;
    logic [1:0]  rw_size;
    logic [1:0]  result_src;
    alu_op_e     alu_ctrl;
    pc_sel_e     pc_sel;
    logic [1:0]  alu_in1_sel;
    logic        alu_in2_sel;
    logic        ld_op_sign;
    logic        rd_csr;
    logic        wr_csr;
    logic [11:0] csr_idx;
    logic        csr_or_data;
    exc_type_e   exc_type;
    logic        dcache_valid;
  } ctrl_t;

  typedef struct packed {
    logic            valid;
    logic            ready;
    logic [XLEN-1:0] addr;
    logic            uncached;
  } icache_req_t;

  typedef struct packed {
    logic                valid;
    logic                ready;
    logic                miss;
    logic [BLK_SIZE-1:0] blk;
  } icache_res_t;

  typedef struct packed {
    logic        valid;
    logic        ready;
    logic [31:0] blk;
  } gbuff_res_t;

  typedef struct packed {
    logic                valid;
    logic                ready;
    logic [BLK_SIZE-1:0] blk;
  } ilowX_res_t;

  typedef struct packed {
    logic            valid;
    logic            ready;
    logic [XLEN-1:0] addr;
    logic            uncached;
  } ilowX_req_t;

  typedef struct packed {
    logic            valid;
    logic            ready;
    logic [XLEN-1:0] addr;
    logic            uncached;
    logic            rw;
    logic [1:0]      rw_size;
    logic [31:0]     data;
  } dcache_req_t;

  typedef struct packed {
    logic        valid;
    logic        miss;
    logic        ready;
    logic [31:0] data;
  } dcache_res_t;

  typedef struct packed {
    logic                valid;
    logic                ready;
    logic [BLK_SIZE-1:0] data;
  } dlowX_res_t;

  typedef struct packed {
    logic                valid;
    logic                ready;
    logic [XLEN-1:0]     addr;
    logic [1:0]          rw_size;
    logic                rw;
    logic [BLK_SIZE-1:0] data;
    logic                uncached;
  } dlowX_req_t;

  typedef struct packed {
    logic            valid;
    logic            ready;
    logic [XLEN-1:0] addr;
    logic            uncached;
  } cache_req_t;

  typedef struct packed {
    logic                valid;
    logic                ready;
    logic [BLK_SIZE-1:0] blk;
  } cache_res_t;

  typedef struct packed {
    logic                valid;
    logic                ready;
    logic [BLK_SIZE-1:0] blk;
  } lowX_res_t;

  typedef struct packed {
    logic            valid;
    logic            ready;
    logic [XLEN-1:0] addr;
    logic            uncached;
  } lowX_req_t;


  typedef struct packed {
    logic                 valid;
    logic                 ready;
    logic [15:0]          rw;
    logic [XLEN-1:0]      addr;
    logic [BLK_SIZE -1:0] data;
  } iomem_req_t;


  typedef struct packed {
    logic                 valid;
    logic                 ready;
    logic [BLK_SIZE -1:0] data;
  } iomem_res_t;


  typedef struct packed {
    logic            valid;
    logic            ready;
    logic [XLEN-1:0] addr;
    logic            uncached;
  } abuff_req_t;

  typedef struct packed {
    logic        valid;
    logic        miss;
    logic        ready;
    logic        waiting_second;  // Double miss: waiting for second cache line
    logic [31:0] blk;
  } abuff_res_t;


  typedef struct packed {
    logic                valid;
    logic                ready;
    logic [BLK_SIZE-1:0] blk;
  } blowX_res_t;

  typedef struct packed {
    logic            valid;
    logic            ready;
    logic [XLEN-1:0] addr;
    logic            uncached;
  } blowX_req_t;


  localparam PHT_SIZE = 128;  // Pattern History Table size (number of entries)
  localparam BTB_SIZE = 128;  // Branch Target Buffer size (number of entries)
  localparam GHR_SIZE = $clog2(PHT_SIZE) + 2;  // Global History logicister size (in bits)


  function automatic logic [XLEN-1:0] trap_cause_decode(input exc_type_e exc);
    case (exc)
      NO_EXCEPTION:        trap_cause_decode = '1;
      //INSTR_MISALIGNED:  trap_cause_decode = 0; // compressed destekleniyorsa kapalı
      INSTR_ACCESS_FAULT:  trap_cause_decode = 1;
      ILLEGAL_INSTRUCTION: trap_cause_decode = 2;
      EBREAK:              trap_cause_decode = 3;
      LOAD_MISALIGNED:     trap_cause_decode = 4;
      LOAD_ACCESS_FAULT:   trap_cause_decode = 5;
      STORE_MISALIGNED:    trap_cause_decode = 6;
      STORE_ACCESS_FAULT:  trap_cause_decode = 7;
      ECALL:               trap_cause_decode = 11;
      default:             trap_cause_decode = '1;
    endcase
  endfunction

  function automatic logic is_supported_csr(input logic [11:0] csr_idx);
    unique case (csr_idx)

      // ============================
      // Mandatory Machine Information
      // ============================
      12'hF11,  // mvendorid
      12'hF12,  // marchid
      12'hF13,  // mimpid
      12'hF14,  // mhartid
      12'hF15,  // mconfigptr

      // ============================
      // Mandatory Trap Setup
      // ============================
      12'h300,  // mstatus
      12'h301,  // misa
      12'h304,  // mie
      12'h305,  // mtvec
      12'h306,  // mcounteren
      12'h310,  // mstatush (RV32 only)

      // ============================
      // Mandatory Trap Handling
      // ============================
      12'h340,  // mscratch
      12'h341,  // mepc
      12'h342,  // mcause
      12'h343,  // mtval
      12'h344,  // mip

      // ============================
      // Counters
      // ============================
      12'hB00,  // mcycle
      12'hB02,  // minstret
      12'hB80,  // mcycleh (RV32)
      12'hB82,  // minstreth (RV32)

      12'h3A0,  // pmpcfg0
      12'h3B0,  // pmpaddr0
      // ============================
      // OPTIONAL CSRs required by tests (read-zero dummy)
      // ============================
      12'h106,  // scounteren
      12'h320,  // mcountinhibit
      12'h7A0,  // tselect
      12'h7A1,  // tdata1
      12'h7A2,  // tdata2
      12'h7A3:  // tdata3

      is_supported_csr = 1'b1;

      default: is_supported_csr = 1'b0;
    endcase
  endfunction

  function string csr_name(input logic [11:0] idx);
    case (idx)

      // Machine Information
      12'hF11: csr_name = "mvendorid";
      12'hF12: csr_name = "marchid";
      12'hF13: csr_name = "mimpid";
      12'hF14: csr_name = "mhartid";
      12'hF15: csr_name = "mconfigptr";

      // Trap Setup
      12'h300: csr_name = "mstatus";
      12'h301: csr_name = "misa";
      12'h304: csr_name = "mie";
      12'h305: csr_name = "mtvec";
      12'h306: csr_name = "mcounteren";
      12'h310: csr_name = "mstatush";

      // Trap Handling
      12'h340: csr_name = "mscratch";
      12'h341: csr_name = "mepc";
      12'h342: csr_name = "mcause";
      12'h343: csr_name = "mtval";
      12'h344: csr_name = "mip";

      // Counters
      12'hB00: csr_name = "mcycle";
      12'hB02: csr_name = "minstret";
      12'hB80: csr_name = "mcycleh";
      12'hB82: csr_name = "minstreth";

      // OPTIONAL — for compliance tests (read-zero)
      12'h106: csr_name = "scounteren";  // read-zero
      12'h320: csr_name = "mcountinhibit";  // read-zero
      12'h3A0: csr_name = "pmpcfg0";  // read-zero
      12'h3B0: csr_name = "pmpaddr0";  // read-zero
      12'h7A0: csr_name = "tselect";  // read-zero
      12'h7A1: csr_name = "tdata1";  // read-zero
      12'h7A2: csr_name = "tdata2";  // read-zero
      12'h7A3: csr_name = "tdata3";  // read-zero

      default: csr_name = $sformatf("csr_%03h", idx);
    endcase
  endfunction


  function automatic logic [XLEN-1:0] csr_wmask(input logic [11:0] idx, input logic [XLEN-1:0] wdata);
    case (idx)

      // mcounteren: tüm bitler WARL → 0 sabit
      12'h306: csr_wmask = '0;

      // scounteren: aynı şekilde 0 sabit
      12'h106: csr_wmask = '0;

      // mip: sadece MIP.MEIP, MIP.MTIP, MIP.MSIP yazılabilir (örneğin)
      12'h344: csr_wmask = wdata & 32'h00000188;

      // mie: yazılabilir alanlar
      12'h304: csr_wmask = wdata & 32'h00000188;

      // mstatus WARL mask (sadece bazı bitler yazılabilir)
      12'h300: csr_wmask = wdata & 32'h00001888;

      // diğer bütün CSR’ler tam yazılabilir
      default: csr_wmask = wdata;

    endcase
  endfunction


  typedef struct packed {
    // High-level
    logic [1:0] MXL;  // misa[31:30]
    logic [3:0] RESERVED;  // misa[29:26]

    // Extension bits 25:0
    logic Z;
    logic Y;
    logic X;
    logic W;
    logic V;
    logic U;
    logic T;
    logic S;
    logic R;
    logic Q;
    logic P;
    logic O;
    logic N;
    logic M;
    logic L;
    logic K;
    logic J;
    logic I;
    logic H;
    logic G;
    logic F;
    logic E;
    logic D;
    logic C;
    logic B;
    logic A;
  } misa_ext_t;

  typedef struct packed {
    logic            valid;
    logic [XLEN-1:0] addr;
    logic            rw;
    logic [1:0]      rw_size;
    logic [31:0]     data;
    logic            ld_op_sign;
  } data_req_t;

  // ============================================================================
  // SoC Memory Map Definitions
  // ============================================================================
  // Standard RISC-V memory regions with room for peripherals
  //
  // 0x0000_0000 - 0x0FFF_FFFF : Reserved / Debug
  // 0x1000_0000 - 0x1FFF_FFFF : Boot ROM (optional)
  // 0x2000_0000 - 0x2FFF_FFFF : Peripheral Region
  //   0x2000_0000 : UART0
  //   0x2000_1000 : UART1
  //   0x2000_2000 : SPI0
  //   0x2000_3000 : I2C0
  //   0x2000_4000 : GPIO
  //   0x2000_5000 : PWM
  //   0x2000_6000 : Timer
  //   0x2000_7000 : Interrupt Controller (PLIC-lite)
  //   0x2000_8000 - 0x2000_FFFF : Reserved for future peripherals
  // 0x3000_0000 - 0x3FFF_FFFF : CLINT (Core Local Interruptor)
  //   0x3000_0000 : msip
  //   0x3000_4000 : mtimecmp
  //   0x3000_BFF8 : mtime
  // 0x4000_0000 - 0x7FFF_FFFF : External Memory / MMIO
  // 0x8000_0000 - 0xFFFF_FFFF : Main RAM

  // Memory Map Base Addresses
  localparam logic [31:0] MMAP_DEBUG_BASE = 32'h0000_0000;
  localparam logic [31:0] MMAP_BOOTROM_BASE = 32'h1000_0000;
  localparam logic [31:0] MMAP_PERIPH_BASE = 32'h2000_0000;
  localparam logic [31:0] MMAP_CLINT_BASE = 32'h3000_0000;
  localparam logic [31:0] MMAP_EXTMEM_BASE = 32'h4000_0000;
  localparam logic [31:0] MMAP_RAM_BASE = 32'h8000_0000;

  // Peripheral Offsets (relative to MMAP_PERIPH_BASE)
  localparam logic [15:0] PERIPH_UART0_OFF = 16'h0000;
  localparam logic [15:0] PERIPH_UART1_OFF = 16'h1000;
  localparam logic [15:0] PERIPH_SPI0_OFF = 16'h2000;
  localparam logic [15:0] PERIPH_I2C0_OFF = 16'h3000;
  localparam logic [15:0] PERIPH_GPIO_OFF = 16'h4000;
  localparam logic [15:0] PERIPH_PWM_OFF = 16'h5000;
  localparam logic [15:0] PERIPH_TIMER_OFF = 16'h6000;
  localparam logic [15:0] PERIPH_PLIC_OFF = 16'h7000;

  // Peripheral slot size (4KB each)
  localparam int PERIPH_SLOT_SIZE = 4096;

  // CLINT Offsets
  localparam logic [15:0] CLINT_MSIP_OFF = 16'h0000;
  localparam logic [15:0] CLINT_MTIMECMP_OFF = 16'h4000;
  localparam logic [15:0] CLINT_MTIME_OFF = 16'hBFF8;

  // ============================================================================
  // Peripheral Bus Interface (Simple, AXI-Lite inspired)
  // ============================================================================
  // Simplified bus for peripheral access - 32-bit only
  typedef struct packed {
    logic        valid;  // Request valid
    logic        ready;  // Requester ready for response
    logic        write;  // 1=write, 0=read
    logic [31:0] addr;   // Byte address
    logic [31:0] wdata;  // Write data
    logic [3:0]  wstrb;  // Write strobes (byte enables)
  } pbus_req_t;

  typedef struct packed {
    logic        valid;  // Response valid
    logic        ready;  // Responder ready
    logic [31:0] rdata;  // Read data
    logic        error;  // Error response
  } pbus_res_t;

  // ============================================================================
  // Interrupt Definitions
  // ============================================================================
  // External interrupt sources (directly mapped to PLIC)
  typedef struct packed {
    logic       uart0_rx;  // UART0 receive interrupt
    logic       uart0_tx;  // UART0 transmit interrupt
    logic       uart1_rx;  // UART1 receive interrupt
    logic       uart1_tx;  // UART1 transmit interrupt
    logic       spi0;      // SPI0 interrupt
    logic       i2c0;      // I2C0 interrupt
    logic       gpio;      // GPIO interrupt (any pin)
    logic       timer;     // Timer interrupt
    logic [7:0] external;  // External interrupt pins
  } ext_irq_t;

  // Number of external interrupt sources
  localparam int NUM_EXT_IRQ = 16;

  // ============================================================================
  // GPIO Configuration
  // ============================================================================
  localparam int GPIO_WIDTH = 32;

  typedef struct packed {
    logic [GPIO_WIDTH-1:0] output_en;   // Output enable (1=output, 0=input)
    logic [GPIO_WIDTH-1:0] output_val;  // Output values
    logic [GPIO_WIDTH-1:0] input_val;   // Input values (directly sampled)
    logic [GPIO_WIDTH-1:0] irq_en;      // Interrupt enable per pin
    logic [GPIO_WIDTH-1:0] irq_edge;    // 1=edge, 0=level triggered
    logic [GPIO_WIDTH-1:0] irq_pol;     // 1=rising/high, 0=falling/low
  } gpio_cfg_t;

endpackage
