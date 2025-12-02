/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

================================================================================
CERES RISC-V — Central Configuration Package
================================================================================
Tüm RTL konfigürasyonu bu dosyada merkezileştirilmiştir.
Modüller bu paketi import ederek parametrelere erişir.

Bölümler:
  1. CORE PARAMETERS      - CPU temel ayarları
  2. CACHE PARAMETERS     - Cache konfigürasyonu
  3. BRANCH PREDICTOR     - Dal tahmin parametreleri
  4. PERIPHERAL           - UART, GPIO, vb.
  5. BUS PARAMETERS       - Wishbone bus ayarları
  6. MEMORY MAP           - Adres haritası
  7. OPCODES              - RISC-V opcode tanımları
  8. ENUMERATIONS         - Tüm enum tipleri
  9. STRUCTURES           - Tüm struct tipleri
  10. FUNCTIONS           - Yardımcı fonksiyonlar
================================================================================
*/
`timescale 1ns / 1ps
`include "ceres_defines.svh"

package ceres_param;

  // ============================================================================
  // 1. CORE PARAMETERS
  // ============================================================================
  localparam int CPU_CLK = 50_000_000;
  localparam int XLEN = 32;
  localparam logic [31:0] RESET_VECTOR = 32'h8000_0000;

  // ============================================================================
  // 2. CACHE PARAMETERS
  // ============================================================================
  localparam int BLK_SIZE = 128;  // Cache block size (bits)

  // Instruction Cache
  localparam int IC_WAY = 8;
  localparam int IC_CAPACITY = 32 * 1024 * 8;  // 32KB (bits)
  localparam int IC_SIZE = IC_CAPACITY / IC_WAY;

  // Data Cache  
  localparam int DC_WAY = 8;
  localparam int DC_CAPACITY = 32 * 1024 * 8;  // 32KB (bits)
  localparam int DC_SIZE = DC_CAPACITY / DC_WAY;

  // Align Buffer (Fetch unit)
  localparam int ABUFF_SIZE = 512;
  localparam int ABUFF_WAY = 1;

  // ============================================================================
  // 3. BRANCH PREDICTOR PARAMETERS
  // ============================================================================
  localparam int PHT_SIZE = 256;  // Pattern History Table entries
  localparam int BTB_SIZE = 128;  // Branch Target Buffer entries
  localparam int GHR_SIZE = 12;  // Global History Register bits
  localparam int IBTC_SIZE = 32;  // Indirect Branch Target Cache
  localparam int RAS_SIZE = 8;  // Return Address Stack depth
  localparam int BP_LOG_INTERVAL = 10000;

  // ============================================================================
  // 4. MULTIPLIER/DIVIDER PARAMETERS
  // ============================================================================
  localparam int MUL_WIDTH = 32;
  localparam int DIV_WIDTH = 32;
  localparam int Mul_Type = 0;  // 0: Wallace, 1: Dadda

  // ============================================================================
  // 5. PERIPHERAL PARAMETERS
  // ============================================================================
  localparam int PROG_BAUD_RATE = 115200;
  localparam PROGRAM_SEQUENCE = "CERESTEST";
  localparam int UART_DATA_WIDTH = 8;
  localparam int UART_TX_FIFO_DEPTH = 256;
  localparam int UART_RX_FIFO_DEPTH = 32;
  localparam int GPIO_WIDTH = 32;
  localparam int NUM_EXT_IRQ = 16;

  // ============================================================================
  // 6. WISHBONE BUS PARAMETERS
  // ============================================================================
  localparam int WB_DATA_WIDTH = 32;
  localparam int WB_ADDR_WIDTH = 32;
  localparam int WB_SEL_WIDTH = WB_DATA_WIDTH / 8;
  localparam int WB_NUM_SLAVES = 4;
  localparam int WB_BURST_LEN = BLK_SIZE / WB_DATA_WIDTH;

  // ============================================================================
  // 7. MEMORY MAP
  // ============================================================================
  // Base Addresses
  localparam logic [31:0] MMAP_DEBUG_BASE = 32'h0000_0000;
  localparam logic [31:0] MMAP_BOOTROM_BASE = 32'h1000_0000;
  localparam logic [31:0] MMAP_PERIPH_BASE = 32'h2000_0000;
  localparam logic [31:0] MMAP_CLINT_BASE = 32'h3000_0000;
  localparam logic [31:0] MMAP_EXTMEM_BASE = 32'h4000_0000;
  localparam logic [31:0] MMAP_RAM_BASE = 32'h8000_0000;

  // Peripheral Offsets
  localparam logic [15:0] PERIPH_UART0_OFF = 16'h0000;
  localparam logic [15:0] PERIPH_UART1_OFF = 16'h1000;
  localparam logic [15:0] PERIPH_SPI0_OFF = 16'h2000;
  localparam logic [15:0] PERIPH_I2C0_OFF = 16'h3000;
  localparam logic [15:0] PERIPH_GPIO_OFF = 16'h4000;
  localparam logic [15:0] PERIPH_PWM_OFF = 16'h5000;
  localparam logic [15:0] PERIPH_TIMER_OFF = 16'h6000;
  localparam logic [15:0] PERIPH_PLIC_OFF = 16'h7000;
  localparam int PERIPH_SLOT_SIZE = 4096;

  // CLINT Offsets
  localparam logic [15:0] CLINT_MSIP_OFF = 16'h0000;
  localparam logic [15:0] CLINT_MTIMECMP_OFF = 16'h4000;
  localparam logic [15:0] CLINT_MTIME_OFF = 16'hBFF8;

  // ============================================================================
  // 8. RISC-V OPCODES
  // ============================================================================
  localparam logic [6:0] system = 7'b11100_11;
  localparam logic [6:0] op_fence_i = 7'b00011_11;
  localparam logic [6:0] op_r_type = 7'b01100_11;
  localparam logic [6:0] op_i_type_load = 7'b00000_11;
  localparam logic [6:0] op_i_type = 7'b00100_11;
  localparam logic [6:0] op_s_type = 7'b01000_11;
  localparam logic [6:0] op_b_type = 7'b11000_11;
  localparam logic [6:0] op_i_type_jump = 7'b11001_11;
  localparam logic [6:0] op_u_type_load = 7'b01101_11;
  localparam logic [6:0] op_u_type_jump = 7'b11011_11;
  localparam logic [6:0] op_u_type_auipc = 7'b00101_11;

  // ============================================================================
  // 9. ENUMERATIONS
  // ============================================================================

  // ---------------------------------------------------------------------------
  // 9.1 Exception Priority Levels
  // ---------------------------------------------------------------------------
  typedef enum logic [4:0] {
    PRIORITY_1,  // Highest
    PRIORITY_2,
    PRIORITY_3,
    PRIORITY_4,
    PRIORITY_5,
    PRIORITY_6,
    PRIORITY_7,  // Lowest
    PRIORITY_DISABLED
  } exc_priority_t;

  localparam exc_priority_t EXC_PRIORITY_DEBUG_BREAKPOINT = PRIORITY_1;
  localparam exc_priority_t EXC_PRIORITY_INSTR_MISALIGNED = PRIORITY_2;
  localparam exc_priority_t EXC_PRIORITY_INSTR_ACCESS_FAULT = PRIORITY_3;
  localparam exc_priority_t EXC_PRIORITY_ILLEGAL = PRIORITY_4;
  localparam exc_priority_t EXC_PRIORITY_EBREAK = PRIORITY_5;
  localparam exc_priority_t EXC_PRIORITY_ECALL = PRIORITY_6;

  // ---------------------------------------------------------------------------
  // 9.2 Speculation Types
  // ---------------------------------------------------------------------------
  typedef enum logic [1:0] {
    NO_SPEC,
    RAS,
    JUMP,
    BRANCH
  } spec_type_e;

  // ---------------------------------------------------------------------------
  // 9.3 Stall Reasons
  // ---------------------------------------------------------------------------
  typedef enum logic [2:0] {
    NO_STALL = 0,
    LOAD_RAW_STALL = 1,
    IMISS_STALL = 2,
    DMISS_STALL = 3,
    ALU_STALL = 4,
    FENCEI_STALL = 5
  } stall_e;

  // ---------------------------------------------------------------------------
  // 9.4 Instruction Types
  // ---------------------------------------------------------------------------
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

  // ---------------------------------------------------------------------------
  // 9.5 Exception Types
  // ---------------------------------------------------------------------------
  typedef enum logic [3:0] {
    INSTR_MISALIGNED,
    INSTR_ACCESS_FAULT,
    ILLEGAL_INSTRUCTION,
    EBREAK,
    BREAKPOINT,
    LOAD_MISALIGNED,
    LOAD_ACCESS_FAULT,
    STORE_MISALIGNED,
    STORE_ACCESS_FAULT,
    ECALL,
    NO_EXCEPTION
  } exc_type_e;

  // ---------------------------------------------------------------------------
  // 9.6 CSR Operations
  // ---------------------------------------------------------------------------
  typedef enum logic [2:0] {
    CSRRW  = 3'h1,
    CSRRS  = 3'h2,
    CSRRC  = 3'h3,
    CSRRWI = 3'h5,
    CSRRSI = 3'h6,
    CSRRCI = 3'h7
  } csr_op_t;

  // ---------------------------------------------------------------------------
  // 9.7 PC Select (Branch/Jump Types)
  // ---------------------------------------------------------------------------
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

  // ---------------------------------------------------------------------------
  // 9.8 Immediate Types
  // ---------------------------------------------------------------------------
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

  // ---------------------------------------------------------------------------
  // 9.9 ALU Operations
  // ---------------------------------------------------------------------------
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

  // ---------------------------------------------------------------------------
  // 9.10 Wishbone Enums
  // ---------------------------------------------------------------------------
  typedef enum logic [2:0] {
    WB_CTI_CLASSIC = 3'b000,
    WB_CTI_CONST   = 3'b001,
    WB_CTI_INCR    = 3'b010,
    WB_CTI_EOB     = 3'b111
  } wb_cti_e;

  typedef enum logic [1:0] {
    WB_BTE_LINEAR = 2'b00,
    WB_BTE_WRAP4  = 2'b01,
    WB_BTE_WRAP8  = 2'b10,
    WB_BTE_WRAP16 = 2'b11
  } wb_bte_e;

  typedef enum logic [3:0] {
    WB_SLAVE_RAM   = 4'h8,
    WB_SLAVE_CLINT = 4'h3,
    WB_SLAVE_PBUS  = 4'h2,
    WB_SLAVE_NONE  = 4'hF
  } wb_slave_sel_e;

  // ============================================================================
  // 10. STRUCTURES
  // ============================================================================

  // ---------------------------------------------------------------------------
  // 10.1 Instruction Format
  // ---------------------------------------------------------------------------
  typedef struct packed {
    logic [6:0] funct7;
    logic [4:0] r2_addr;
    logic [4:0] r1_addr;
    logic [2:0] funct3;
    logic [4:0] rd_addr;
    logic [6:0] opcode;
  } inst_t;

  // ---------------------------------------------------------------------------
  // 10.2 Tracer Info
  // ---------------------------------------------------------------------------
  typedef struct packed {
    logic [XLEN-1:0] pc;
    logic [XLEN-1:0] inst;
    logic [63:0]     sn;
  } fe_tracer_info_t;

  // ---------------------------------------------------------------------------
  // 10.3 Return Address Stack
  // ---------------------------------------------------------------------------
  typedef struct packed {
    logic            valid;
    logic [XLEN-1:0] data;
  } ras_t;

  // ---------------------------------------------------------------------------
  // 10.4 Branch Prediction
  // ---------------------------------------------------------------------------
  typedef struct packed {
    logic            taken;
    logic [XLEN-1:0] pc;
    spec_type_e      spectype;
  } predict_info_t;

  // ---------------------------------------------------------------------------
  // 10.5 Pipeline Structures
  // ---------------------------------------------------------------------------
  typedef struct packed {
    exc_type_e       exc_type;
    predict_info_t   spec;
    pc_sel_e         bjtype;
    logic [XLEN-1:0] pc;
  } pipe_info_t;

  // Fetch -> Decode
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

  // Decode -> Execute
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
    logic [4:0]      rd_addr;
    logic [XLEN-1:0] imm;
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

  // Execute -> Memory
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

  // Memory -> Writeback
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

  // ---------------------------------------------------------------------------
  // 10.6 Control Signals
  // ---------------------------------------------------------------------------
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

  // ---------------------------------------------------------------------------
  // 10.7 Cache Interfaces
  // ---------------------------------------------------------------------------
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

  // ---------------------------------------------------------------------------
  // 10.8 Lower Level Memory Interface
  // ---------------------------------------------------------------------------
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
    logic        valid;
    logic        ready;
    logic [31:0] blk;
  } gbuff_res_t;

  // ---------------------------------------------------------------------------
  // 10.9 Align Buffer Interface
  // ---------------------------------------------------------------------------
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
    logic        waiting_second;
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

  // ---------------------------------------------------------------------------
  // 10.10 IO/Memory Interface
  // ---------------------------------------------------------------------------
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
    logic [XLEN-1:0] addr;
    logic            rw;
    logic [1:0]      rw_size;
    logic [31:0]     data;
    logic            ld_op_sign;
  } data_req_t;

  // ---------------------------------------------------------------------------
  // 10.11 Wishbone Bus
  // ---------------------------------------------------------------------------
  typedef struct packed {
    logic [WB_ADDR_WIDTH-1:0] adr;
    logic [WB_DATA_WIDTH-1:0] dat;
    logic [WB_SEL_WIDTH-1:0]  sel;
    logic                     we;
    logic                     stb;
    logic                     cyc;
    wb_cti_e                  cti;
    wb_bte_e                  bte;
  } wb_master_t;

  typedef struct packed {
    logic [WB_DATA_WIDTH-1:0] dat;
    logic                     ack;
    logic                     err;
    logic                     rty;
    logic                     stall;
  } wb_slave_t;

  // ---------------------------------------------------------------------------
  // 10.12 Peripheral Bus
  // ---------------------------------------------------------------------------
  typedef struct packed {
    logic        valid;
    logic        ready;
    logic        write;
    logic [31:0] addr;
    logic [31:0] wdata;
    logic [3:0]  wstrb;
  } pbus_req_t;

  typedef struct packed {
    logic        valid;
    logic        ready;
    logic [31:0] rdata;
    logic        error;
  } pbus_res_t;

  // ---------------------------------------------------------------------------
  // 10.13 Interrupts
  // ---------------------------------------------------------------------------
  typedef struct packed {
    logic       uart0_rx;
    logic       uart0_tx;
    logic       uart1_rx;
    logic       uart1_tx;
    logic       spi0;
    logic       i2c0;
    logic       gpio;
    logic       timer;
    logic [7:0] external;
  } ext_irq_t;

  // ---------------------------------------------------------------------------
  // 10.14 GPIO
  // ---------------------------------------------------------------------------
  typedef struct packed {
    logic [GPIO_WIDTH-1:0] output_en;
    logic [GPIO_WIDTH-1:0] output_val;
    logic [GPIO_WIDTH-1:0] input_val;
    logic [GPIO_WIDTH-1:0] irq_en;
    logic [GPIO_WIDTH-1:0] irq_edge;
    logic [GPIO_WIDTH-1:0] irq_pol;
  } gpio_cfg_t;

  // ---------------------------------------------------------------------------
  // 10.15 MISA Extension
  // ---------------------------------------------------------------------------
  typedef struct packed {
    logic [1:0] MXL;
    logic [3:0] RESERVED;
    logic Z, Y, X, W, V, U, T, S, R, Q, P, O, N, M;
    logic L, K, J, I, H, G, F, E, D, C, B, A;
  } misa_ext_t;

  // ============================================================================
  // 11. FUNCTIONS
  // ============================================================================

  // ---------------------------------------------------------------------------
  // 11.1 Exception Priority Check
  // ---------------------------------------------------------------------------
  function automatic logic check_exc_priority(input exc_priority_t exc_pri, input exc_priority_t min_pri);
    return (exc_pri <= min_pri) && (exc_pri != PRIORITY_DISABLED);
  endfunction

  // ---------------------------------------------------------------------------
  // 11.2 Instruction Type Resolver
  // ---------------------------------------------------------------------------
  function instr_type_e resolved_instr_type;
    input inst_t inst_i;
    case (inst_i.opcode)
      op_fence_i: begin
        if (inst_i.funct3 == '0) resolved_instr_type = fence;
        else if (inst_i.funct3 == 3'b001) resolved_instr_type = fence_i;
        else resolved_instr_type = instr_invalid;
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
      default:         resolved_instr_type = instr_invalid;
    endcase
    return resolved_instr_type;
  endfunction

  // ---------------------------------------------------------------------------
  // 11.3 Branch Type Detector
  // ---------------------------------------------------------------------------
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

  // ---------------------------------------------------------------------------
  // 11.4 Trap Cause Decoder
  // ---------------------------------------------------------------------------
  function automatic logic [XLEN-1:0] trap_cause_decode(input exc_type_e exc);
    case (exc)
      NO_EXCEPTION:        trap_cause_decode = '1;
      INSTR_ACCESS_FAULT:  trap_cause_decode = 1;
      ILLEGAL_INSTRUCTION: trap_cause_decode = 2;
      EBREAK:              trap_cause_decode = 3;
      BREAKPOINT:          trap_cause_decode = 3;
      LOAD_MISALIGNED:     trap_cause_decode = 4;
      LOAD_ACCESS_FAULT:   trap_cause_decode = 5;
      STORE_MISALIGNED:    trap_cause_decode = 6;
      STORE_ACCESS_FAULT:  trap_cause_decode = 7;
      ECALL:               trap_cause_decode = 11;
      default:             trap_cause_decode = '1;
    endcase
  endfunction

  // ---------------------------------------------------------------------------
  // 11.5 CSR Support Checker
  // ---------------------------------------------------------------------------
  function automatic logic is_supported_csr(input logic [11:0] csr_idx);
    unique case (csr_idx)
      12'hF11, 12'hF12, 12'hF13, 12'hF14, 12'hF15,
      12'h300, 12'h301, 12'h304, 12'h305, 12'h306, 12'h310,
      12'h340, 12'h341, 12'h342, 12'h343, 12'h344,
      12'hB00, 12'hB02, 12'hB80, 12'hB82,
      12'hC00, 12'hC02, 12'hC80, 12'hC82,
      12'h3A0, 12'h3B0,
      12'h106, 12'h320, 12'h7A0, 12'h7A1, 12'h7A2, 12'h7A3, 12'h7A5:
      is_supported_csr = 1'b1;
      default: is_supported_csr = 1'b0;
    endcase
  endfunction

  // ---------------------------------------------------------------------------
  // 11.6 CSR Name Decoder
  // ---------------------------------------------------------------------------
  function string csr_name(input logic [11:0] idx);
    case (idx)
      12'hF11: csr_name = "mvendorid";
      12'hF12: csr_name = "marchid";
      12'hF13: csr_name = "mimpid";
      12'hF14: csr_name = "mhartid";
      12'hF15: csr_name = "mconfigptr";
      12'h300: csr_name = "mstatus";
      12'h301: csr_name = "misa";
      12'h304: csr_name = "mie";
      12'h305: csr_name = "mtvec";
      12'h306: csr_name = "mcounteren";
      12'h310: csr_name = "mstatush";
      12'h340: csr_name = "mscratch";
      12'h341: csr_name = "mepc";
      12'h342: csr_name = "mcause";
      12'h343: csr_name = "mtval";
      12'h344: csr_name = "mip";
      12'hB00: csr_name = "mcycle";
      12'hB02: csr_name = "minstret";
      12'hB80: csr_name = "mcycleh";
      12'hB82: csr_name = "minstreth";
      12'h106: csr_name = "scounteren";
      12'h320: csr_name = "mcountinhibit";
      12'h3A0: csr_name = "pmpcfg0";
      12'h3B0: csr_name = "pmpaddr0";
      12'h7A0: csr_name = "tselect";
      12'h7A1: csr_name = "tdata1";
      12'h7A2: csr_name = "tdata2";
      12'h7A3: csr_name = "tdata3";
      12'h7A5: csr_name = "tcontrol";
      default: csr_name = $sformatf("csr_%03h", idx);
    endcase
  endfunction

  // ---------------------------------------------------------------------------
  // 11.7 CSR Write Mask (WARL)
  // ---------------------------------------------------------------------------
  function automatic logic [XLEN-1:0] csr_wmask(input logic [11:0] idx, input logic [XLEN-1:0] wdata);
    case (idx)
      12'h306: csr_wmask = '0;
      12'h106: csr_wmask = '0;
      12'h344: csr_wmask = wdata & 32'h00000188;
      12'h304: csr_wmask = wdata & 32'h00000188;
      12'h300: csr_wmask = wdata & 32'h00001888;
      default: csr_wmask = wdata;
    endcase
  endfunction

endpackage
