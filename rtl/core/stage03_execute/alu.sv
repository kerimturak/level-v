/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
`include "ceres_defines.svh"

module alu
  import ceres_param::*;
(
    input  logic               clk_i,
    input  logic               rst_ni,
    input  logic    [XLEN-1:0] csr_rdata_i,
    input  logic    [XLEN-1:0] alu_a_i,
    input  logic    [XLEN-1:0] alu_b_i,
    input  alu_op_e            op_sel_i,
    output logic               alu_stall_o,
    output logic               zero_o,
    output logic               slt_o,
    output logic               sltu_o,
    output logic    [XLEN-1:0] alu_o
);

  // ------------------------------------------------------------
  // ALU sonuçları
  // ------------------------------------------------------------
  typedef struct packed {
    logic [XLEN-1:0]   ADD;
    logic [XLEN-1:0]   SLT;
    logic [XLEN-1:0]   SLTU;
    logic [XLEN-1:0]   AND;
    logic [XLEN-1:0]   OR;
    logic [XLEN-1:0]   XOR;
    logic [XLEN-1:0]   SLL;
    logic [XLEN-1:0]   SRL;
    logic [XLEN-1:0]   SUB;
    logic [XLEN-1:0]   SRA;
    logic [XLEN-1:0]   LUI;
    logic [XLEN-1:0]   DIV;
    logic [XLEN-1:0]   DIVU;
    logic [XLEN-1:0]   REM;
    logic [XLEN-1:0]   REMU;
    logic [XLEN-1:0]   MUL;
    logic [2*XLEN-1:0] MULH;
    logic [2*XLEN-1:0] MULHSU;
    logic [2*XLEN-1:0] MULHU;
  } result_t;

  result_t              rslt;

  // ------------------------------------------------------------
  // Ortak sinyaller
  // ------------------------------------------------------------
  logic    [  XLEN-1:0] abs_A;
  logic    [  XLEN-1:0] abs_B;

  logic                 mul_type;
  logic                 div_type;

  // signed/unsigned için ayrı sign bitleri
  logic                 mul_sign;  // çarpımın işareti
  logic                 div_sign_quot;  // bölümün işareti (DIV)
  logic                 div_sign_rem;  // kalanın işareti (REM)

  logic                 mul_start;
  logic                 div_start;

  logic    [  XLEN-1:0] mul_op_A;
  logic    [  XLEN-1:0] mul_op_B;
  logic    [  XLEN-1:0] div_op_A;
  logic    [  XLEN-1:0] div_op_B;

  logic    [2*XLEN-1:0] product;
  logic    [  XLEN-1:0] quotient;
  logic    [  XLEN-1:0] remainder;

  logic                 mul_stall;
  logic                 div_stall;
  logic                 alu_stall_q;
  logic                 mul_busy;
  logic                 div_busy;
  logic                 mul_valid;
  logic                 div_valid;

  logic    [2*XLEN-1:0] unsigned_prod;
  logic    [  XLEN-1:0] unsigned_quo;
  logic    [  XLEN-1:0] unsigned_rem;

  logic                 mul_done;
  logic                 div_done;
  logic                 div_dbz;

  // sonrasında RISC-V kurallarına göre düzeltilmiş bölüm/kalan
  logic    [  XLEN-1:0] div_quot_final;
  logic    [  XLEN-1:0] div_rem_final;

  // ------------------------------------------------------------
  // Ortak abs ve type hesapları
  // ------------------------------------------------------------
  always_comb begin
    // Mutlak değerler (signed için)
    abs_A         = alu_a_i[XLEN-1] ? ~alu_a_i + 1'b1 : alu_a_i;
    abs_B         = alu_b_i[XLEN-1] ? ~alu_b_i + 1'b1 : alu_b_i;

    mul_type      = (op_sel_i inside {[OP_MUL : OP_MULHU]});
    div_type      = (op_sel_i inside {[OP_DIV : OP_REMU]});

    // Varsayılanlar
    mul_sign      = 1'b0;
    div_sign_quot = 1'b0;
    div_sign_rem  = 1'b0;

    // Varsayılan operandlar
    mul_op_A      = abs_A;
    mul_op_B      = abs_B;
    div_op_A      = abs_A;
    div_op_B      = abs_B;

    // ------------------------
    // MUL / MULH / MULHSU / MULHU
    // ------------------------
    if (mul_type) begin
      unique case (op_sel_i)
        // rs1, rs2 signed → sign = rs1^rs2
        OP_MUL, OP_MULH: begin
          mul_op_A = abs_A;
          mul_op_B = abs_B;
          mul_sign = alu_a_i[XLEN-1] ^ alu_b_i[XLEN-1];
        end

        // rs1 signed, rs2 unsigned → sign = rs1[MSB]
        OP_MULHSU: begin
          mul_op_A = abs_A;  // |rs1|
          mul_op_B = alu_b_i;  // rs2 zaten unsigned
          mul_sign = alu_a_i[XLEN-1];
        end

        // rs1, rs2 unsigned → sign yok
        OP_MULHU: begin
          mul_op_A = alu_a_i;
          mul_op_B = alu_b_i;
          mul_sign = 1'b0;
        end

        default: begin
          mul_op_A = abs_A;
          mul_op_B = abs_B;
          mul_sign = 1'b0;
        end
      endcase
    end

    // ------------------------
    // DIV / DIVU / REM / REMU
    // ------------------------
    if (div_type) begin
      unique case (op_sel_i)
        // rs1, rs2 signed
        OP_DIV, OP_REM: begin
          div_op_A      = abs_A;
          div_op_B      = abs_B;
          div_sign_quot = alu_a_i[XLEN-1] ^ alu_b_i[XLEN-1];  // quotient sign
          div_sign_rem  = alu_a_i[XLEN-1];  // remainder sign = sign(rs1)
        end

        // rs1, rs2 unsigned → sign yok
        OP_DIVU, OP_REMU: begin
          div_op_A      = alu_a_i;
          div_op_B      = alu_b_i;
          div_sign_quot = 1'b0;
          div_sign_rem  = 1'b0;
        end

        default: begin
          div_op_A      = abs_A;
          div_op_B      = abs_B;
          div_sign_quot = 1'b0;
          div_sign_rem  = 1'b0;
        end
      endcase
    end

    // Başlatma sinyalleri
    mul_start = mul_type && !mul_busy && !(alu_stall_q);
    div_start = div_type && !div_busy && !(alu_stall_q & !div_dbz);

    // ÇARPMA sign düzeltmesi (two's complement)
    // unsigned_prod = |opA| * |opB| / veya unsigned*unsigned
    product   = mul_sign ? -unsigned_prod : unsigned_prod;

    // BÖLME sign düzeltmesi (two's complement) — sadece signed ops için
    quotient  = div_sign_quot ? -unsigned_quo : unsigned_quo;
    remainder = div_sign_rem ? -unsigned_rem : unsigned_rem;

    // Stall mantığı (senin mantığını koruyorum)
    mul_stall = (mul_type && !mul_valid) || (mul_valid && mul_start);
    div_stall = (div_type && !div_valid) || (div_valid && div_start);
    div_stall &= !div_dbz;
    alu_stall_o = mul_stall || div_stall;
  end

  // ------------------------------------------------------------
  // Stall register
  // ------------------------------------------------------------
  always_ff @(posedge clk_i) begin
    if (!rst_ni) alu_stall_q <= 1'b0;
    else alu_stall_q <= alu_stall_o;
  end

  // ------------------------------------------------------------
  // Multiplication unit
  // Priority: PIPELINED > WALLACE_SINGLE > DSP > Sequential
  // ------------------------------------------------------------
`ifdef FEAT_PIPELINED_MUL
  // Pipelined multiplier for improved timing (2 cycles, breaks deep comb logic)
  mul_pipelined #(
      .XLEN(32),
      .YLEN(32)
  ) i_mul_pipelined (
      .clk_i    (clk_i),
      .rst_ni   (rst_ni),
      .start_i  (mul_start),
      .a_i      (mul_op_A),
      .b_i      (mul_op_B),
      .product_o(unsigned_prod),
      .busy_o   (mul_busy),
      .done_o   (mul_done),
      .valid_o  (mul_valid)
  );

`elsif FEAT_WALLACE_SINGLE
  // Single-cycle Wallace/Dadda tree (fast but deep combinational logic)
  assign mul_valid = 1'b1;
  assign mul_busy  = 1'b0;

  mul #(
      .XLEN(32),
      .YLEN(32),
      .TYP (Mul_Type)
  ) i_mul (
      .a(mul_op_A),
      .b(mul_op_B),
      .c(unsigned_prod)
  );

`elsif FEAT_DSP_MUL
  // DSP block multiplier (uses FPGA DSP slices)
  always_comb begin
    unsigned_prod = mul_op_A * mul_op_B;
    mul_valid     = 1'b1;
    mul_busy      = 1'b0;
  end

`else
  // Sequential multiplier (32 cycles, smallest area)
  seq_multiplier #(
      .SIZE(32)
  ) i_seq_multiplier (
      .clk_i         (clk_i),
      .rst_ni        (rst_ni),
      .start_i       (mul_start),
      .busy_o        (mul_busy),
      .done_o        (mul_done),
      .valid_o       (mul_valid),
      .multiplicand_i(mul_op_A),
      .multiplier_i  (mul_op_B),
      .product_o     (unsigned_prod)
  );

`endif

  // ------------------------------------------------------------
  // Division unit (unsigned core)
  // Select between original (divu_int) or pipelined version (divu_pipelined)
  // ------------------------------------------------------------
`ifdef FEAT_PIPELINED_DIV
  // Pipelined division for improved timing (2 bits/cycle, 16 cycles total)
  divu_pipelined #(
      .WIDTH(32),
      .BITS_PER_CYCLE(2)
  ) i_divu_pipelined (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .start_i   (div_start),
      .busy_o    (div_busy),
      .done_o    (div_done),
      .valid_o   (div_valid),
      .dbz_o     (div_dbz),
      .dividend_i(div_op_A),
      .divisor_i (div_op_B),
      .quotient_o(unsigned_quo),
      .reminder_o(unsigned_rem)
  );
`else
  // Original sequential division (1 bit/cycle, 32 cycles total)
  divu_int #(
      .WIDTH(32)
  ) i_divu_int (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .start_i   (div_start),
      .busy_o    (div_busy),
      .done_o    (div_done),
      .valid_o   (div_valid),
      .dbz_o     (div_dbz),
      .dividend_i(div_op_A),
      .divisor_i (div_op_B),
      .quotient_o(unsigned_quo),
      .reminder_o(unsigned_rem)
  );
`endif

  // ------------------------------------------------------------
  // RISC-V DIV/REM final düzeltmeleri (dbz + signed/unsigned)
  // ------------------------------------------------------------
  always_comb begin
    // QUOTIENT
    if (div_dbz) begin
      // DIV/DIVU by zero → quotient = -1 (0xFFFFFFFF)
      if (op_sel_i inside {OP_DIV, OP_DIVU}) div_quot_final = 32'hFFFF_FFFF;
      else div_quot_final = unsigned_quo;  // undefined; çok önemli değil
    end else if (op_sel_i == OP_DIVU || op_sel_i == OP_REMU) begin
      // Unsigned ops
      div_quot_final = unsigned_quo;
    end else begin
      // Signed DIV
      div_quot_final = quotient;
    end

    // REMAINDER
    if (div_dbz) begin
      // DIV/REM by zero → remainder = rs1 (spec)
      div_rem_final = alu_a_i;
    end else if (op_sel_i == OP_DIVU || op_sel_i == OP_REMU) begin
      div_rem_final = unsigned_rem;
    end else begin
      div_rem_final = remainder;  // sign(rs1) ile düzeltilmiş
    end
  end

  // ------------------------------------------------------------
  // Normal ALU operasyonları + M sonuçları
  // ------------------------------------------------------------
  always_comb begin
    rslt.ADD    = alu_a_i + alu_b_i;
    rslt.SUB    = alu_a_i - alu_b_i;
    rslt.SLT    = ($signed(alu_a_i) < $signed(alu_b_i)) ? 32'b1 : 32'b0;
    rslt.SLTU   = (alu_a_i < alu_b_i) ? 32'b1 : 32'b0;
    rslt.AND    = alu_a_i & alu_b_i;
    rslt.OR     = alu_a_i | alu_b_i;
    rslt.XOR    = alu_a_i ^ alu_b_i;
    rslt.SLL    = alu_a_i << alu_b_i[4:0];
    rslt.SRL    = alu_a_i >> alu_b_i[4:0];
    rslt.SRA    = $signed(alu_a_i) >>> alu_b_i[4:0];
    rslt.LUI    = alu_b_i;

    // MULTIPLY sonuçları
    rslt.MUL    = product[31:0];  // low 32 bit
    rslt.MULH   = product;  // signed×signed (üstten alınacak)
    rslt.MULHSU = product;  // signed×unsigned
    rslt.MULHU  = unsigned_prod;  // pure unsigned çarpım

    // DIV/REM sonuçları
    rslt.DIV    = div_quot_final;
    rslt.DIVU   = div_dbz ? '1 : unsigned_quo;
    rslt.REM    = div_rem_final;
    rslt.REMU   = unsigned_rem;

    // Sonuç mux
    unique case (op_sel_i)
      OP_ADD:  alu_o = rslt.ADD;
      OP_SUB:  alu_o = rslt.SUB;
      OP_SLL:  alu_o = rslt.SLL;
      OP_SLT:  alu_o = rslt.SLT;
      OP_SLTU: alu_o = rslt.SLTU;
      OP_XOR:  alu_o = rslt.XOR;
      OP_SRL:  alu_o = rslt.SRL;
      OP_SRA:  alu_o = rslt.SRA;
      OP_OR:   alu_o = rslt.OR;
      OP_AND:  alu_o = rslt.AND;

      OP_MUL:    alu_o = rslt.MUL;
      OP_MULH:   alu_o = rslt.MULH[2*XLEN-1:XLEN];
      OP_MULHSU: alu_o = rslt.MULHSU[2*XLEN-1:XLEN];
      OP_MULHU:  alu_o = rslt.MULHU[2*XLEN-1:XLEN];

      OP_DIV:  alu_o = rslt.DIV;
      OP_DIVU: alu_o = rslt.DIVU;
      OP_REM:  alu_o = rslt.REM;
      OP_REMU: alu_o = rslt.REMU;

      OP_LUI: alu_o = rslt.LUI;

      OP_CSRRW:  alu_o = alu_a_i;
      OP_CSRRS:  alu_o = csr_rdata_i | alu_a_i;
      OP_CSRRC:  alu_o = csr_rdata_i & ~alu_a_i;
      OP_CSRRWI: alu_o = alu_b_i;
      OP_CSRRSI: alu_o = csr_rdata_i | alu_b_i;
      OP_CSRRCI: alu_o = csr_rdata_i & ~alu_b_i;

      default: alu_o = '0;
    endcase

    // Flags
    zero_o = ($signed(alu_a_i) == $signed(alu_b_i));
    slt_o  = ($signed(alu_a_i) < $signed(alu_b_i));
    sltu_o = ($unsigned(alu_a_i) < $unsigned(alu_b_i));
  end

endmodule
