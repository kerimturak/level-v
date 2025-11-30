/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
`include "ceres_defines.svh"

module cs_reg_file
  import ceres_param::*;
(
    input logic   clk_i,
    input logic   rst_ni,
    input stall_e stall_i,

    input  logic            rd_en_i,
    input  logic            wr_en_i,
    input  logic [    11:0] csr_idx_i,
    input  logic [XLEN-1:0] csr_wdata_i,
    output logic [XLEN-1:0] csr_rdata_o,

    input  logic                   trap_active_i,
    input  logic                   de_trap_active_i,
    input  instr_type_e            instr_type_i,
    input  logic        [XLEN-1:0] trap_cause_i,
    input  logic        [XLEN-1:0] trap_mepc_i,
    input  logic        [XLEN-1:0] trap_tval_i,
    output logic        [XLEN-1:0] mtvec_o,
    output logic        [XLEN-1:0] mepc_o,
    output logic                   misa_c_o,
    // Trigger/Debug outputs for hardware breakpoint
    output logic        [XLEN-1:0] tdata1_o,
    output logic        [XLEN-1:0] tdata2_o
);

  /*
   * MINIMAL M-MODE CSR SET (RISC-V Privileged Spec v1.12)
   *
   * MANDATORY:
   *   mvendorid, marchid, mimpid, mhartid, mconfigptr (read-only-zero OK)
   *   mstatus, misa, mie, mtvec, mcounteren
   *   mscratch, mepc, mcause, mtval, mip
   *   mcycle, minstret (+ mcycleh, minstreth for RV32)
   *
   * OPTIONAL (implemented as read-only-zero for test compatibility):
   *   scounteren, mcountinhibit, pmpcfg0, pmpaddr0
   *   tselect, tdata1, tdata2, tdata3
   */

  // ============================================================================
  // CSR ADDRESS DEFINITIONS
  // ============================================================================
  
  // Machine Information Registers
  localparam logic [11:0] MVENDORID  = 12'hF11;
  localparam logic [11:0] MARCHID    = 12'hF12;
  localparam logic [11:0] MIMPID     = 12'hF13;
  localparam logic [11:0] MHARTID    = 12'hF14;
  localparam logic [11:0] MCONFIGPTR = 12'hF15;

  // Machine Trap Setup
  localparam logic [11:0] MSTATUS    = 12'h300;
  localparam logic [11:0] MISA       = 12'h301;
  localparam logic [11:0] MIE_ADDR   = 12'h304;
  localparam logic [11:0] MTVEC      = 12'h305;
  localparam logic [11:0] MCOUNTEREN = 12'h306;
  localparam logic [11:0] MSTATUSH   = 12'h310;

  // Machine Trap Handling
  localparam logic [11:0] MSCRATCH = 12'h340;
  localparam logic [11:0] MEPC     = 12'h341;
  localparam logic [11:0] MCAUSE   = 12'h342;
  localparam logic [11:0] MTVAL    = 12'h343;
  localparam logic [11:0] MIP      = 12'h344;

  // Machine Counter/Timers
  localparam logic [11:0] MCYCLE    = 12'hB00;
  localparam logic [11:0] MINSTRET  = 12'hB02;
  localparam logic [11:0] MCYCLEH   = 12'hB80;
  localparam logic [11:0] MINSTRETH = 12'hB82;

  // User-mode Counter Shadow Registers (read-only aliases)
  localparam logic [11:0] CYCLE     = 12'hC00;
  localparam logic [11:0] INSTRET   = 12'hC02;
  localparam logic [11:0] CYCLEH    = 12'hC80;
  localparam logic [11:0] INSTRETH  = 12'hC82;

  // Optional CSRs (read-only-zero for test compatibility)
  localparam logic [11:0] SCOUNTEREN    = 12'h106;
  localparam logic [11:0] MCOUNTINHIBIT = 12'h320;
  localparam logic [11:0] PMPCFG0       = 12'h3A0;
  localparam logic [11:0] PMPADDR0      = 12'h3B0;
  localparam logic [11:0] TSELECT       = 12'h7A0;
  localparam logic [11:0] TDATA1        = 12'h7A1;
  localparam logic [11:0] TDATA2        = 12'h7A2;
  localparam logic [11:0] TDATA3        = 12'h7A3;
  localparam logic [11:0] TCONTROL      = 12'h7A5;

  // ============================================================================
  // MISA CONFIGURATION (RV32IMC)
  // ============================================================================
  
  localparam misa_ext_t CERES_MISA = '{
      MXL      : 2'b01,  // RV32
      RESERVED : '0,
      Z : 1'b0,  // bit25
      Y : 1'b0,  // bit24
      X : 1'b0,  // bit23
      W : 1'b0,  // bit22
      V : 1'b0,  // bit21
      U : 1'b0,  // bit20
      T : 1'b0,  // bit19
      S : 1'b0,  // bit18
      R : 1'b0,  // bit17
      Q : 1'b0,  // bit16
      P : 1'b0,  // bit15
      O : 1'b0,  // bit14
      N : 1'b0,  // bit13
      M : 1'b1,  // bit12
      L : 1'b0,  // bit11
      K : 1'b0,  // bit10
      J : 1'b0,  // bit 9
      I : 1'b1,  // bit 8
      H : 1'b0,  // bit 7
      G : 1'b0,  // bit 6
      F : 1'b0,  // bit 5
      E : 1'b0,  // bit 4
      D : 1'b0,  // bit 3
      C : 1'b1,  // bit 2
      B : 1'b0,  // bit 1
      A : 1'b0   // bit 0
  };

  // MISA WARL mask: only C extension bit is writable
  localparam logic [XLEN-1:0] MISA_WRITABLE_MASK = 32'h0000_0004;

  // ============================================================================
  // MSTATUS STRUCTURE (Minimal M-mode only)
  // ============================================================================
  
  typedef struct packed {
    logic       mie;   // Machine Interrupt Enable
    logic       mpie;  // Previous MIE (saved during trap)
    logic [1:0] mpp;   // Previous Privilege Mode (always 2'b11 for M-mode)
  } mstatus_t;

  // M-mode interrupt enable mask: MSIE(3), MTIE(7), MEIE(11)
  localparam logic [XLEN-1:0] MIE_RW_MASK = 32'h0000_0888;

  // MIP is read-only in minimal implementation (HW sets pending bits)
  localparam logic [XLEN-1:0] MIP_RW_MASK = 32'h0000_0000;

  // ============================================================================
  // MSTATUS PACK/UNPACK FUNCTIONS
  // ============================================================================
  
  function automatic logic [31:0] pack_mstatus(mstatus_t m);
    logic [31:0] d;
    d        = 32'd0;
    d[3]     = m.mie;
    d[7]     = m.mpie;
    d[12:11] = m.mpp;
    return d;
  endfunction

  function automatic mstatus_t unpack_mstatus(logic [31:0] d);
    // M-mode only system: MPP is WARL, always reads as 2'b11 (M-mode)
    // Writes to MPP bits are ignored
    return '{mie: d[3], mpie: d[7], mpp: 2'b11};
  endfunction

  // ============================================================================
  // CSR REGISTERS
  // ============================================================================
  
  mstatus_t mstatus;
  misa_ext_t misa;
  
  logic [XLEN-1:0] mie;
  logic [XLEN-1:0] mtvec;
  logic [XLEN-1:0] mip;
  logic [XLEN-1:0] mscratch;
  logic [XLEN-1:0] mepc;
  logic [XLEN-1:0] mcause;
  logic [XLEN-1:0] mtval_reg;

  // 64-bit performance counters (split for RV32)
  logic [XLEN-1:0] mcycle;
  logic [XLEN-1:0] mcycleh;
  logic [XLEN-1:0] minstret;
  logic [XLEN-1:0] minstreth;

  logic     [XLEN-1:0] pmpcfg0;
  logic     [XLEN-1:0] pmpaddr0;
  logic     [XLEN-1:0] tcontrol_reg;  // Trigger control register
  logic     [XLEN-1:0] tdata1_reg;    // Trigger data 1 register
  logic     [XLEN-1:0] tdata2_reg;    // Trigger data 2 register (breakpoint address)
  // ============================================================================
  // OUTPUT ASSIGNMENTS
  // ============================================================================
  
  always_comb begin
    misa_c_o = misa.C;
    // mtvec write bypass (benchmark için)
    mtvec_o  = (csr_idx_i == 12'h305 && wr_en_i && de_trap_active_i) ? csr_wdata_i : mtvec;
    mepc_o   = mepc;
    // Trigger outputs for hardware breakpoint detection
    tdata1_o = tdata1_reg;
    tdata2_o = tdata2_reg;
  end

  // ============================================================================
  // CSR STATE + PERFORMANCE COUNTERS UPDATE
  // ============================================================================
  
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      // Reset all CSRs
      mstatus   <= '{mie: 1'b0, mpie: 1'b0, mpp: 2'b11};  // M-mode only: start in M-mode
      misa      <= CERES_MISA;
      mie       <= '0;
      mtvec     <= '0;
      mip       <= '0;
      mscratch  <= '0;
      mepc      <= '0;
      mcause    <= '0;
      mtval_reg <= '0;

      // Reset counters
      mcycle    <= '0;
      mcycleh   <= '0;
      minstret  <= '0;
      minstreth <= '0;
      pmpcfg0   <= '0;
      pmpaddr0  <= '0;
      tcontrol_reg <= '0;
      tdata1_reg <= 32'h20000044;  // Default: mcontrol type
      tdata2_reg <= '0;

    end else if (!(stall_i inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL} && !trap_active_i)) begin
      
      // ------------------------------------------------------------------------
      // PERFORMANCE COUNTERS (always increment unless stalled)
      // ------------------------------------------------------------------------
      
      // mcycle/mcycleh: increment every active cycle
      {mcycleh, mcycle} <= {mcycleh, mcycle} + 64'd1;

      // minstret/minstreth: increment only when instruction retires
      // Skip increment if we're writing to minstret/minstreth (to match Spike timing)
      if (!trap_active_i && !(wr_en_i && (csr_idx_i == MINSTRET || csr_idx_i == MINSTRETH))) begin
        {minstreth, minstret} <= {minstreth, minstret} + 64'd1;
      end

      // ------------------------------------------------------------------------
      // TRAP ENTRY (highest priority)
      // ------------------------------------------------------------------------
      
      if (de_trap_active_i) begin
        mepc         <= trap_mepc_i;
        mcause       <= trap_cause_i;
        mtval_reg    <= trap_tval_i;
        mstatus.mpie <= mstatus.mie;
        mstatus.mie  <= 1'b0;
        mstatus.mpp  <= 2'b11;  // M-mode
      end else if (trap_active_i && !de_trap_active_i) begin
        mepc         <= trap_mepc_i;
        mcause       <= trap_cause_i;
        mtval_reg    <= trap_tval_i;
        mstatus.mpie <= mstatus.mie;
        mstatus.mie  <= 1'b0;
        mstatus.mpp  <= 2'b11;  // M-mode
      end
      
      // ------------------------------------------------------------------------
      // MRET (trap return)
      // ------------------------------------------------------------------------
      
      else if (instr_type_i == mret) begin
        mstatus.mie  <= mstatus.mpie;
        mstatus.mpie <= 1'b1;
        mstatus.mpp  <= 2'b11;  // M-mode only: always return to M-mode
      end
      
      // ------------------------------------------------------------------------
      // NORMAL CSR WRITE
      // ------------------------------------------------------------------------
      
      else if (wr_en_i) begin
        unique case (csr_idx_i)

          // Trap Setup Registers
          MSTATUS: mstatus <= unpack_mstatus(csr_wdata_i);

          MISA: begin
            // WARL: only C extension bit is writable
            misa <= misa_ext_t'((misa & ~MISA_WRITABLE_MASK) | (csr_wdata_i & MISA_WRITABLE_MASK));
          end

          MIE_ADDR: mie   <= (mie & ~MIE_RW_MASK) | (csr_wdata_i & MIE_RW_MASK);
          MTVEC:    mtvec <= csr_wdata_i;

          // Trap Handling Registers
          MIP:      mip       <= (mip & ~MIP_RW_MASK) | (csr_wdata_i & MIP_RW_MASK);
          MSCRATCH: mscratch  <= csr_wdata_i;
          MEPC:     mepc      <= csr_wdata_i;
          MCAUSE:   mcause    <= csr_wdata_i;
          MTVAL:    mtval_reg <= csr_wdata_i;

          // Performance Counters (writable per RISC-V spec)
          MCYCLE:    mcycle    <= csr_wdata_i;
          MCYCLEH:   mcycleh   <= csr_wdata_i;
          MINSTRET:  minstret  <= csr_wdata_i;
          MINSTRETH: minstreth <= csr_wdata_i;

          // Optional CSRs: writes ignored (read-only-zero behavior)
          MCOUNTEREN,
          SCOUNTEREN,
          MCOUNTINHIBIT,
          //PMPCFG0,
          //PMPADDR0,
          TSELECT,
          TDATA3: ;  // No-op
          TDATA1:   tdata1_reg <= csr_wdata_i;  // Trigger data 1 (writable)
          TDATA2:   tdata2_reg <= csr_wdata_i;  // Trigger data 2 (breakpoint address)
          TCONTROL: tcontrol_reg <= csr_wdata_i;  // Trigger control (writable)
          PMPCFG0:  pmpcfg0  <= csr_wdata_i;  // şimdilik düz RW
          PMPADDR0: pmpaddr0 <= csr_wdata_i;  // şimdilik düz RW
          default: ;  // Unsupported CSR: ignore write
        endcase
      end

    end
  end

  // ============================================================================
  // CSR READ LOGIC
  // ============================================================================
  
  always_comb begin
    if (rd_en_i) begin
      unique case (csr_idx_i)

        // Machine Information Registers (read-only-zero)
        MVENDORID:  csr_rdata_o = 32'd0;
        MARCHID:    csr_rdata_o = 32'd5;  // Match Spike for test compatibility
        MIMPID:     csr_rdata_o = 32'd0;
        MHARTID:    csr_rdata_o = 32'd0;
        MCONFIGPTR: csr_rdata_o = 32'd0;

        // Trap Setup
        MSTATUS:  csr_rdata_o = pack_mstatus(mstatus);
        MSTATUSH: csr_rdata_o = 32'd0;  // RV32 extension (not used)
        MISA:     csr_rdata_o = misa;

        // Interrupt Control
        MIE_ADDR: csr_rdata_o = mie;
        MTVEC:    csr_rdata_o = mtvec;
        MIP:      csr_rdata_o = mip;

        // Trap Handling
        MSCRATCH: csr_rdata_o = mscratch;
        MEPC:     csr_rdata_o = mepc;
        MCAUSE:   csr_rdata_o = mcause;
        MTVAL:    csr_rdata_o = mtval_reg;

        // Performance Counters (Machine)
        MCYCLE:    csr_rdata_o = mcycle;
        MCYCLEH:   csr_rdata_o = mcycleh;
        MINSTRET:  csr_rdata_o = minstret;
        MINSTRETH: csr_rdata_o = minstreth;

        // User-mode Counter Shadows (read-only aliases to M-mode counters)
        CYCLE:     csr_rdata_o = mcycle;
        CYCLEH:    csr_rdata_o = mcycleh;
        INSTRET:   csr_rdata_o = minstret;
        INSTRETH:  csr_rdata_o = minstreth;

        // Optional CSRs (read-only-zero)
        MCOUNTEREN,
        SCOUNTEREN,
        MCOUNTINHIBIT,
        //PMPCFG0,
        //PMPADDR0,
        TSELECT,
        TDATA3: csr_rdata_o = 32'd0;
        // tdata1: Return written value (writable trigger data)
        TDATA1:   csr_rdata_o = tdata1_reg;
        TDATA2:   csr_rdata_o = tdata2_reg;  // Breakpoint address
        TCONTROL: csr_rdata_o = tcontrol_reg;  // Return written value
        PMPCFG0:  csr_rdata_o = pmpcfg0;
        PMPADDR0: csr_rdata_o = pmpaddr0;
        default: csr_rdata_o = 32'd0;  // Unsupported CSR
      endcase
      
    end else begin
      // Special case: MRET needs to read updated mstatus value
      if (instr_type_i == mret) begin
        csr_rdata_o = pack_mstatus('{mie: mstatus.mpie, mpie: 1'b1, mpp: 2'b11});  // M-mode only
      end else begin
        csr_rdata_o = 32'd0;
      end
    end
  end

endmodule
