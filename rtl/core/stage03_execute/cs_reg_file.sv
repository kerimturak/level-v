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
    input  logic        [XLEN-1:0] pc_i,           // Current PC for MISA write check
    // Hardware interrupt inputs
    input  logic                   timer_irq_i,    // CLINT timer interrupt (MTIP)
    input  logic                   sw_irq_i,       // CLINT software interrupt (MSIP)
    input  logic                   ext_irq_i,      // PLIC external interrupt (MEIP)
    output logic        [XLEN-1:0] mtvec_o,
    output logic        [XLEN-1:0] mepc_o,
    output logic                   misa_c_o,
`ifdef COMMIT_TRACER
    output logic                   csr_write_valid_o,  // CSR write was accepted (not rejected)
`endif
    // Trigger/Debug outputs for hardware breakpoint (both triggers)
    output logic        [XLEN-1:0] tdata1_o[0:1],
    output logic        [XLEN-1:0] tdata2_o[0:1],
    output logic        [XLEN-1:0] tcontrol_o
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
  // Bit 3: MSIP (Software Interrupt Pending)
  // Bit 7: MTIP (Timer Interrupt Pending)  
  // Bit 11: MEIP (External Interrupt Pending)
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
  logic     [XLEN-1:0] tselect_reg;   // Trigger select register (0 or 1)
  logic     [XLEN-1:0] tcontrol_reg;  // Trigger control register
  logic     [XLEN-1:0] tdata1_reg[0:1];  // Trigger 0 and 1 data1 registers
  logic     [XLEN-1:0] tdata2_reg[0:1];  // Trigger 0 and 1 data2 registers
  logic     [XLEN-1:0] tcontrol_out_reg;  // Registered output to break combinational loop
  // ============================================================================
  // OUTPUT ASSIGNMENTS
  // ============================================================================

  // ============================================================================
  // MIP Register - Hardware Interrupt Pending Bits
  // ============================================================================
  // MIP bits are set by hardware interrupt sources:
  //   Bit 3 (MSIP): Software interrupt from CLINT
  //   Bit 7 (MTIP): Timer interrupt from CLINT (mtime >= mtimecmp)
  //   Bit 11 (MEIP): External interrupt from PLIC
  // These bits are read-only to software - they reflect hardware state
  always_comb begin
    mip = '0;
    mip[3]  = sw_irq_i;      // MSIP - Machine Software Interrupt Pending
    mip[7]  = timer_irq_i;   // MTIP - Machine Timer Interrupt Pending
    mip[11] = ext_irq_i;     // MEIP - Machine External Interrupt Pending
  end
  
  // ============================================================================
  // Write-through bypass for trigger registers
  // Allows same-cycle visibility of written values
  // ============================================================================
  logic [XLEN-1:0] tdata1_bypass;
  logic [XLEN-1:0] tdata2_bypass;
  logic [XLEN-1:0] tcontrol_bypass;
  logic [XLEN-1:0] tselect_safe;  // Safe tselect value (clamped to 0 or 1)

  always_comb begin
    // Clamp tselect to valid range [0:1]
    tselect_safe = (tselect_reg > 1) ? 32'd0 : tselect_reg;

    // Write-through bypass: if writing this cycle, use write data, else use register
    // Select based on tselect (or tselect being written)
    if (wr_en_i && csr_idx_i == TDATA1) begin
      tdata1_bypass = csr_wdata_i;
    end else begin
      tdata1_bypass = tdata1_reg[tselect_safe[0]];
    end

    if (wr_en_i && csr_idx_i == TDATA2) begin
      tdata2_bypass = csr_wdata_i;
    end else begin
      tdata2_bypass = tdata2_reg[tselect_safe[0]];
    end

    tcontrol_bypass = (wr_en_i && csr_idx_i == TCONTROL) ? csr_wdata_i : tcontrol_reg;
  end

  always_comb begin
    misa_c_o = misa.C;
    // mtvec write bypass (benchmark için)
    mtvec_o  = (csr_idx_i == 12'h305 && wr_en_i && de_trap_active_i) ? csr_wdata_i : mtvec;
    // mepc output with alignment mask (Spike-compatible)
    // Clear low bits based on current MISA.C: bit[0] always, bit[1] if C disabled
    if (misa.C)
      mepc_o = {mepc[XLEN-1:1], 1'b0};        // 2-byte align
    else
      mepc_o = {mepc[XLEN-1:2], 2'b00};       // 4-byte align
`ifdef COMMIT_TRACER
    // CSR write validity check - MISA write can be rejected
    if (wr_en_i && csr_idx_i == MISA && !csr_wdata_i[2] && misa.C && pc_i[1])
      csr_write_valid_o = 1'b0;  // MISA write rejected (can't disable C when PC misaligned)
    else
      csr_write_valid_o = 1'b1;  // All other writes accepted
`endif
    // Trigger outputs: Output both triggers with bypass logic
    // Trigger 0
    if (wr_en_i && csr_idx_i == TDATA1 && tselect_safe[0] == 1'b0) begin
      tdata1_o[0] = csr_wdata_i;
    end else begin
      tdata1_o[0] = tdata1_reg[0];
    end
    if (wr_en_i && csr_idx_i == TDATA2 && tselect_safe[0] == 1'b0) begin
      tdata2_o[0] = csr_wdata_i;
    end else begin
      tdata2_o[0] = tdata2_reg[0];
    end
    // Trigger 1
    if (wr_en_i && csr_idx_i == TDATA1 && tselect_safe[0] == 1'b1) begin
      tdata1_o[1] = csr_wdata_i;
    end else begin
      tdata1_o[1] = tdata1_reg[1];
    end
    if (wr_en_i && csr_idx_i == TDATA2 && tselect_safe[0] == 1'b1) begin
      tdata2_o[1] = csr_wdata_i;
    end else begin
      tdata2_o[1] = tdata2_reg[1];
    end
    tcontrol_o = tcontrol_out_reg;  // KEY: Use registered value (breaks combinational loop)
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
      // Note: mip is now combinational - driven by hardware interrupt sources
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
      tselect_reg <= '0;
      tcontrol_reg <= '0;
      tcontrol_out_reg <= '0;  // Initialize registered output
      tdata1_reg[0] <= 32'h20000044;  // Trigger 0: mcontrol type
      tdata1_reg[1] <= 32'h20000044;  // Trigger 1: mcontrol type
      tdata2_reg[0] <= '0;
      tdata2_reg[1] <= '0;

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
        // Trigger control: save mte to mpte
        tcontrol_reg[7] <= tcontrol_reg[3];  // mpte = mte
      end else if (trap_active_i && !de_trap_active_i) begin
        mepc         <= trap_mepc_i;
        mcause       <= trap_cause_i;
        mtval_reg    <= trap_tval_i;
        mstatus.mpie <= mstatus.mie;
        mstatus.mie  <= 1'b0;
        mstatus.mpp  <= 2'b11;  // M-mode
        // Trigger control: save mte to mpte
        tcontrol_reg[7] <= tcontrol_reg[3];  // mpte = mte
      end
      
      // ------------------------------------------------------------------------
      // MRET (trap return)
      // ------------------------------------------------------------------------

      else if (instr_type_i == mret) begin
        mstatus.mie  <= mstatus.mpie;
        mstatus.mpie <= 1'b1;
        mstatus.mpp  <= 2'b11;  // M-mode only: always return to M-mode
        // Trigger control: mte = mpte (mpte is NOT cleared on MRET per spec)
        tcontrol_reg[3] <= tcontrol_reg[7];  // mte = mpte
        // mpte remains unchanged
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
            // Spike-compatible behavior: Reject C extension disable if PC is misaligned
            // Reject write if: disabling C (new=0, old=1) && PC[1]=1 (misaligned)
            if (!csr_wdata_i[2] && misa.C && pc_i[1]) begin
              // Write rejected - keep old value (PC is 2-byte aligned, can't disable C)
              misa <= misa;
            end else begin
              // Write accepted
              misa <= misa_ext_t'((misa & ~MISA_WRITABLE_MASK) | (csr_wdata_i & MISA_WRITABLE_MASK));
            end
          end

          MIE_ADDR: mie   <= (mie & ~MIE_RW_MASK) | (csr_wdata_i & MIE_RW_MASK);
          MTVEC:    mtvec <= csr_wdata_i;

          // Trap Handling Registers
          // Note: MIP is read-only - hardware interrupt sources set the pending bits
          MSCRATCH: mscratch  <= csr_wdata_i;
          MEPC: begin
            // Spike-compatible: Only clear bit[0] on write, alignment mask applied on read
            mepc <= {csr_wdata_i[XLEN-1:1], 1'b0};
          end
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
          TDATA3: ;  // No-op
          TSELECT:  begin
            // WARL: Only accept 0 or 1, clamp to 0 if out of range
            tselect_reg <= (csr_wdata_i > 1) ? 32'd0 : csr_wdata_i;
          end
          // TDATA1/TDATA2: Write to selected trigger (0 or 1)
          TDATA1: begin
            if (tselect_safe[0] == 1'b0)
              tdata1_reg[0] <= csr_wdata_i;
            else
              tdata1_reg[1] <= csr_wdata_i;
          end
          TDATA2: begin
            if (tselect_safe[0] == 1'b0)
              tdata2_reg[0] <= csr_wdata_i;
            else
              tdata2_reg[1] <= csr_wdata_i;
          end
          TCONTROL: tcontrol_reg <= csr_wdata_i;  // Trigger control (writable)
          PMPCFG0:  pmpcfg0  <= csr_wdata_i;  // şimdilik düz RW
          PMPADDR0: pmpaddr0 <= csr_wdata_i;  // şimdilik düz RW
          default: ;  // Unsupported CSR: ignore write
        endcase
      end

    end

    // ------------------------------------------------------------------------
    // UPDATE tcontrol_out_reg (sequential logic breaks combinational loop)
    // ------------------------------------------------------------------------
    // This must happen EVERY cycle (not just on trap/mret/write) to track changes
    // Placed outside stall condition to ensure it updates even during stalls

    if (trap_active_i || de_trap_active_i) begin
      // On trap entry: save mte to mpte
      tcontrol_out_reg[7]   <= tcontrol_bypass[3];  // mpte = mte
      tcontrol_out_reg[3]   <= tcontrol_bypass[3];  // mte unchanged
      tcontrol_out_reg[6:4] <= '0;
      tcontrol_out_reg[2:0] <= '0;
      tcontrol_out_reg[31:8] <= '0;
    end else if (instr_type_i == mret) begin
      // On MRET: restore mte from mpte
      tcontrol_out_reg[7]   <= tcontrol_bypass[7];  // mpte unchanged
      tcontrol_out_reg[3]   <= tcontrol_bypass[7];  // mte = mpte
      tcontrol_out_reg[6:4] <= '0;
      tcontrol_out_reg[2:0] <= '0;
      tcontrol_out_reg[31:8] <= '0;
    end else begin
      // Normal operation: track bypass value (includes CSR writes via bypass)
      tcontrol_out_reg <= tcontrol_bypass;
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
        TDATA3: csr_rdata_o = 32'd0;
        // TSELECT: Read back written value (0 or 1)
        TSELECT:  csr_rdata_o = tselect_reg;
        // TDATA1/TDATA2: Return selected trigger's values
        TDATA1:   csr_rdata_o = tdata1_reg[tselect_safe[0]];
        TDATA2:   csr_rdata_o = tdata2_reg[tselect_safe[0]];
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
