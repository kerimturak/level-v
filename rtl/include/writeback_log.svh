// ============================================================================
// Spike-like Commit Trace — Ceres RISC-V
// Engineer:  Kerim Turak
// ----------------------------------------------------------------------------
// Production order (Spike-compatible):
//   1. CSR write (wr_en_csr_i)
//   2. Memory write
//   3. Register writeback
//   4. No-write instruction
// ============================================================================

integer trace_fd;
string  trace_path;
string  test_name;
string  simulator;

`ifdef VERILATOR
`define SOC $root.ceres_wrapper.soc
`else
`define SOC tb_wrapper.ceres_wrapper.soc
`endif

// ============================================================================
// INITIAL (open trace file)
// ============================================================================
initial begin
  if (!$value$plusargs("simulator=%s", simulator))
    simulator = "default_simulator";

  if (!$value$plusargs("test_name=%s", test_name))
    test_name = "default_test";

  if (!$value$plusargs("trace_file=%s", trace_path))
    trace_path = $sformatf("/home/kerim/riscv_git/ceres-riscv/results/logs/%0s/%0s/commit_trace.log",
                            simulator, test_name);

  void'($system($sformatf("mkdir -p $(dirname %s)", trace_path)));

  trace_fd = $fopen(trace_path, "wb");
  if (trace_fd == 0) begin
    $display("[ERROR] Failed to open trace file: %s", trace_path);
    $finish;
  end
end

// ============================================================================
// MAIN TRACE LOGIC (Spike EXACT behavior)
// ============================================================================
always @(posedge clk_i) begin
  if (!rst_ni) begin
    if (trace_fd != 0) $fclose(trace_fd);
    trace_fd <= $fopen(trace_path, "w");
  end
  
  else if (!(stall_i inside {IMISS_STALL, DMISS_STALL, ALU_STALL} && !trap_active_i)) begin

    // ============================================================
    // 1) SPIKE-STYLE: CSR + RD WRITE IN SAME INSTRUCTION (CSRRW / CSRRS / CSRRC)
    // ============================================================
    if ((instr_type_i inside {CSR_RW, CSR_RS, CSR_RC, CSR_RWI, CSR_RSI, CSR_RCI}) &&
        wr_en_csr_i && rf_rw_en_i && rd_addr_i != 0) begin

      // Format:
      // core 0: 3 PC (INST) x<rd> oldCSR  c<idx>_name newCSR
      $fwrite(trace_fd,
        "core   0: 3 0x%08h (0x%08h) x%0d 0x%08h c%0d_%s 0x%08h\n",
        pc_i,
        fe_tracer_i.inst,
        rd_addr_i,
        wb_data_o,                     // RD = OLD CSR
        csr_idx_i,
        csr_name(csr_idx_i),
        csr_wr_data_i                  // CSR = NEW CSR (your new port)
      );
    end

// ============================================================
// SPECIAL CASE — MRET implicit CSR writes
// Spike logs both mstatus (0x300) and mstatush (0x310) on MRET.
// ============================================================
else if (instr_type_i == mret) begin : mret_commit

    // mstatus
    $fwrite(trace_fd,
      "core   0: 3 0x%08h (0x%08h) c%0d_mstatus 0x%08h ",
      pc_i, fe_tracer_i.inst,
      768,        // <<2 doğru
      csr_wr_data_i
    );

    // mstatush
    $fwrite(trace_fd,
      "c%0d_mstatush 0x00000000\n",
      784         // <<2 doğru
    );

    disable mret_commit;
end



    // ============================================================
    // 2) CSR WRITE ONLY (CSRWI, CSRRW x0,csr)
    // ============================================================
    else if (wr_en_csr_i) begin
      $fwrite(trace_fd,
        "core   0: 3 0x%08h (0x%08h) c%0d_%s 0x%08h\n",
        pc_i, fe_tracer_i.inst,
        csr_idx_i,
        csr_name(csr_idx_i),
        csr_wr_data_i
      );
    end

    // ============================================================
    // 3) REGISTER WRITE ONLY (normal ALU, load result, jump-link, etc.)
    // ============================================================
    else if (instr_type_i inside {i_lb, i_lh, i_lw, i_lbu, i_lhu}) begin
      automatic string spacing = (rd_addr_i < 10) ? "  " : " ";
      $fwrite(trace_fd,
        "core    0: 3 0x%08h (0x%08h) x%0d%s0x%08h mem 0x%08h\n",
        pc_i, fe_tracer_i.inst,
        rd_addr_i, spacing, wb_data_o,
        alu_result_i
      );
    end

    else if (rf_rw_en_i && rd_addr_i != 0) begin
      automatic string spacing = (rd_addr_i < 10) ? "  " : " ";
      $fwrite(trace_fd,
        "core   0: 3 0x%08h (0x%08h) x%0d%s0x%08h\n",
        pc_i, fe_tracer_i.inst,
        rd_addr_i, spacing, wb_data_o
      );
    end

    // ============================================================
    // 4) MEMORY WRITE (store)
    // ============================================================
    else if (instr_type_i inside {s_sb, s_sh, s_sw}) begin
      automatic logic [31:0] wdata = write_data_i;

      case (rw_size_i)
        2'b01:
          $fwrite(trace_fd,
            "core   0: 3 0x%08h (0x%08h) mem 0x%08h 0x%02h\n",
            pc_i, fe_tracer_i.inst, alu_result_i, wdata[7:0]);

        2'b10:
          $fwrite(trace_fd,
            "core   0: 3 0x%08h (0x%08h) mem 0x%08h 0x%04h\n",
            pc_i, fe_tracer_i.inst, alu_result_i, wdata[15:0]);

        2'b11:
          $fwrite(trace_fd,
            "core   0: 3 0x%08h (0x%08h) mem 0x%08h 0x%08h\n",
            pc_i, fe_tracer_i.inst, alu_result_i, wdata[31:0]);
      endcase
    end

    // ============================================================
    // 5) NO-WRITE INSTRUCTION
    // ============================================================
    else begin
      $fwrite(trace_fd,
        "core   0: 3 0x%08h (0x%08h)\n",
        pc_i, fe_tracer_i.inst
      );
    end
  end
end

// ==========================================================
// PASS/FAIL Address Detector (from per-test addr.txt file)
// ==========================================================

string addr_file;
logic [31:0] pass_addr, fail_addr;
integer fd, r;

initial begin
  // Dosya ismini +arg ile al: +addr_file=/path/to/test_addr.txt
  if (!$value$plusargs("addr_file=%s", addr_file)) begin
    $display(" No +addr_file given. Skipping PASS/FAIL auto-stop.");
    if (test_name == "rv32ui-p-simple") begin
      pass_addr = 32'h8000013c;
      fail_addr = 32'h80000140;
    end else begin
      pass_addr = 32'h0;
      fail_addr = 32'h0;
    end
  end else begin
    fd = $fopen(addr_file, "r");
    if (fd == 0) begin
      $display("ERROR: cannot open %s", addr_file);
      pass_addr = 32'h0;
      fail_addr = 32'h0;
    end else begin
      r = $fscanf(fd, "%h %h", pass_addr, fail_addr);
      $fclose(fd);
      $display("Loaded PASS/FAIL addresses: PASS=0x%08h FAIL=0x%08h", pass_addr, fail_addr);
    end
  end
end

// Writeback veya memory stage içinde:
`ifndef CERES_UART_TX_MONITOR
always_comb begin
  if (pc_i == pass_addr) begin
    $display("🎯 PASS address reached at PC=0x%08h", pc_i);
    $fclose(fd);
    $finish;
  end else if (pc_i == fail_addr) begin
    $display("FAIL address reached at PC=0x%08h", pc_i);
    $fclose(fd);
    $finish;
  end
end

task automatic check_pass_fail();
  if (pass_addr != 32'h0 && pc_i == pass_addr) begin
    $display("PASS reached at PC=0x%08h", pc_i);
    $finish;
  end
  if (fail_addr != 32'h0 && pc_i == fail_addr) begin
    $display("FAIL reached at PC=0x%08h", pc_i);
    $finish;
  end
endtask

always @(posedge clk_i) begin
  automatic logic        we = wr_en_i;
  automatic logic        valid = `SOC.pipe4.dcache_valid;
  automatic logic [31:0] addr = `SOC.pipe4.alu_result;
  automatic logic [31:0] data = `SOC.pipe4.write_data;

  if (valid && we && addr == 32'h80001000) begin
    if (data == 32'h1) begin
      $display("🎉 TOHOST PASS");
      $finish;
    end else begin
      $display("❌ TOHOST FAIL (0x%08h)", data);
      $finish;
    end
  end
end

`endif

final begin
  if (trace_fd != 0) $fclose(trace_fd);
end