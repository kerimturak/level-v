// ============================================================================
// Ceres Pipeline Logger — KONATA v0004
//  - Front (F/D) ve Back (X/M/Wb) için ayrı advance mantığı
//  - Stage başı:  S
//  - Stage sonu:  E
//  - Issue:       I + L (pc:instr)
//  - Retire:      R (flush=0) veya R (flush=1)
//  - Ek bilgiler:
//      * grp=ALU/LOAD/STORE/BRANCH/JUMP/CSR/SYSCALL/PRIV/FENCE
//      * stall=NONE/IMISS/DMISS/RAW/ALU/OTHER
//      * stall_cycles=N   (instr pipeline'da toplam kaç cycle stall gördü)
//      * mem_latency=N    (LOAD/STORE için M stage'de kaç cycle bekledi)
//
// Enable with: +define+KONATA_TRACER
// ============================================================================
`ifndef KONATA_LOGGER_SV

`timescale 1ns / 1ps
`include "ceres_defines.svh"

`ifdef KONATA_TRACER

module konata_logger;

  integer fd;
  string  log_path;

`ifdef VERILATOR
  `define SOC $root.ceres_wrapper.i_soc
`else
  `define SOC tb_wrapper.ceres_wrapper.i_soc
`endif

  // ----------------------------------------------------------------------------
  // Dosya açma & header
  // ----------------------------------------------------------------------------
  initial begin
    if (!$value$plusargs("log_path=%s", log_path)) log_path = "/home/kerim/github/riscv/ceres-riscv/results/logs/rtl/ceres.KONATA";

    void'($system($sformatf("mkdir -p $(dirname %s)", log_path)));

    fd = $fopen(log_path, "w");
    if (fd == 0) begin
      $display("❌ [konata_logger] Cannot open %s", log_path);
      $finish;
    end

    $fwrite(fd, "KONATA\t0004\n");
    $display("✅ [konata_logger] Started: %s", log_path);
  end

  // ----------------------------------------------------------------------------
  // Yardımcı fonksiyonlar: instr_group & stall string
  // ----------------------------------------------------------------------------

  // Instr tipinden "grp=" etiketi
  function string instr_group(input instr_type_e t);
    unique case (t)
      // LOAD
      i_lb, i_lh, i_lw, i_lbu, i_lhu: instr_group = "LOAD";

      // STORE
      s_sb, s_sh, s_sw: instr_group = "STORE";

      // BRANCH
      b_beq, b_bne, b_blt, b_bge, b_bltu, b_bgeu: instr_group = "BRANCH";

      // JUMP
      u_jal, i_jalr: instr_group = "JUMP";

      // CSR
      CSR_RW, CSR_RS, CSR_RC, CSR_RWI, CSR_RSI, CSR_RCI: instr_group = "CSR";

      // SYSCALL / TRAP benzeri
      ecall, ebreak: instr_group = "SYSCALL";

      // PRIV
      mret, wfi: instr_group = "PRIV";

      // FENCE
      fence_i: instr_group = "FENCE";

      // Default: ALU / diğer her şey
      default: instr_group = "ALU";
    endcase
  endfunction

  // Instr memory access mi?
  function bit is_mem_instr(input instr_type_e t);
    unique case (t)
      i_lb, i_lh, i_lw, i_lbu, i_lhu, s_sb, s_sh, s_sw: is_mem_instr = 1'b1;
      default:                                          is_mem_instr = 1'b0;
    endcase
  endfunction

  // Stall sebebini string'e çevir
  function string stall_to_str(input stall_e s);
    unique case (s)
      NO_STALL:       stall_to_str = "NONE";
      IMISS_STALL:    stall_to_str = "IMISS";
      DMISS_STALL:    stall_to_str = "DMISS";
      LOAD_RAW_STALL: stall_to_str = "RAW";
      ALU_STALL:      stall_to_str = "ALU";
      default:        stall_to_str = "OTHER";
    endcase
  endfunction

  // ----------------------------------------------------------------------------
  // Pipeline stage state (logger tarafı)
  // ----------------------------------------------------------------------------
  typedef struct {
    integer      id;
    logic [31:0] pc;
    logic [31:0] inst;
    logic        valid;
    logic        started_f;
    logic        started_d;
    logic        started_x;
    logic        started_m;
    logic        started_wb;

    // Ek bilgiler
    instr_type_e instr_type;        // CPU fetch'ten gelen instr_type_o
    integer      stall_cycles;      // toplam stall (front+back)
    integer      mem_stall_cycles;  // sadece M stage'de LOAD/STORE beklemeleri
    stall_e      first_stall;       // ilk stall sebebi
    logic        retired;           // R yazıldı mı? (re-retire spam'i engellemek için)
  } pipe_entry_t;

  pipe_entry_t fetch_s, decode_s, execute_s, memory_s, writeback_s;
  pipe_entry_t prev_fetch, prev_decode, prev_execute, prev_memory, prev_writeback;

  longint cycle_cnt = 0;
  logic   first_cycle = 1'b1;
  integer next_id = 0;

  // ----------------------------------------------------------------------------
  // Emit helper fonksiyonları
  // ----------------------------------------------------------------------------
  function void log_stage_start(input integer id, input string stg);
    if (fd != 0) $fwrite(fd, "S\t%0d\t0\t%s\n", id, stg);
  endfunction

  function void log_stage_end(input integer id, input string stg);
    if (fd != 0) $fwrite(fd, "E\t%0d\t0\t%s\n", id, stg);
  endfunction

  function void log_issue(input integer id);
    if (fd != 0) $fwrite(fd, "I\t%0d\t%0d\t0\n", id, id);
  endfunction

  function void log_line_pc_inst(input integer id, input logic [31:0] pc, input logic [31:0] inst);
    if (fd != 0) $fwrite(fd, "L\t%0d\t0\t%08h: %08h\n", id, pc, inst);
  endfunction

  function void log_retire(input integer id);
    if (fd != 0) $fwrite(fd, "R\t%0d\t%0d\t0\n", id, id);
  endfunction

  function void log_retire_flush(input integer id);
    if (fd != 0) $fwrite(fd, "R\t%0d\t%0d\t1\n", id, id);
  endfunction

  // ----------------------------------------------------------------------------
  // Ana logger
  // ----------------------------------------------------------------------------
  // Front (F/D) ve Back (X/M/Wb) için ayrı advance sinyalleri
  logic adv_front;  // F + D (stall_cause == NO_STALL)
  logic adv_back;  // X + M + Wb (stall_cause NOT in {IMISS, DMISS, ALU})
  logic flush_fe;
  logic wb_closed;  // sadece flush case'inde kullanılıyor, şu an struct'ı sıfırlamıyoruz

  // Fetch tarafı
  logic fetch_valid_int;
  logic fetch_buf_valid;
  logic fetch_enter;

  // O cycle’da stage enter edenler
  logic d_enter_now;
  logic x_enter_now;
  logic m_enter_now;
  logic wb_enter_now;

  always @(posedge `SOC.clk_i) begin
    flush_fe  = `SOC.i_fetch.flush_i;

    // CPU tarafı ile birebir:
    //  - Front: FETCH & pipe1 sadece NO_STALL iken ilerliyor
    //  - Back:  pipe2/3/4 sadece IMISS/DMISS/ALU iken duruyor
    adv_front = (`SOC.stall_cause == NO_STALL);
    adv_back  = !(`SOC.stall_cause inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL});

    wb_closed = 1'b0;

    if (!`SOC.rst_ni) begin
      cycle_cnt   <= 0;
      first_cycle <= 1'b1;
      fetch_s     <= '{first_stall: NO_STALL, instr_type: Null_Instr_Type, default: 0};
      decode_s    <= '{first_stall: NO_STALL, instr_type: Null_Instr_Type, default: 0};
      execute_s   <= '{first_stall: NO_STALL, instr_type: Null_Instr_Type, default: 0};
      memory_s    <= '{first_stall: NO_STALL, instr_type: Null_Instr_Type, default: 0};
      writeback_s <= '{first_stall: NO_STALL, instr_type: Null_Instr_Type, default: 0};
    end else begin
      // ----------------------------------------------------------------------
      // 1) Cycle header
      // ----------------------------------------------------------------------
      if (first_cycle) begin
        $fwrite(fd, "C=\t%0d\n", cycle_cnt);
        first_cycle <= 1'b0;
      end else begin
        $fwrite(fd, "C\t1\n");
      end

      // ----------------------------------------------------------------------
      // 2) Snapshot (prev_* bu cycle'ın eski state'i)
      // ----------------------------------------------------------------------
      prev_fetch     = fetch_s;
      prev_decode    = decode_s;
      prev_execute   = execute_s;
      prev_memory    = memory_s;
      prev_writeback = writeback_s;

      // ----------------------------------------------------------------------
      // 3) Stall sayaçları
      //    - flush cycle'ında sayma, çünkü o anda zaten pipeline boşaltılıyor
      // ----------------------------------------------------------------------
      if (!flush_fe) begin
        // Front (F + D) stall
        if (!adv_front) begin
          if (fetch_s.valid) fetch_s.stall_cycles++;
          if (decode_s.valid) decode_s.stall_cycles++;
        end

        // Back (X + M + Wb) stall
        if (!adv_back) begin
          if (execute_s.valid) execute_s.stall_cycles++;
          if (memory_s.valid) memory_s.stall_cycles++;
          if (writeback_s.valid) writeback_s.stall_cycles++;

          // Memory stage'de LOAD/STORE için ekstra mem_stall_cycles
          if (memory_s.valid && is_mem_instr(memory_s.instr_type)) memory_s.mem_stall_cycles++;
        end

        // İlk stall sebebi (instr pipeline'a girdiğinden beri ilk kez stall olduğu anda kaydet)
        if (`SOC.stall_cause != NO_STALL) begin
          if (fetch_s.valid && fetch_s.first_stall == NO_STALL) fetch_s.first_stall = `SOC.stall_cause;
          if (decode_s.valid && decode_s.first_stall == NO_STALL) decode_s.first_stall = `SOC.stall_cause;
          if (execute_s.valid && execute_s.first_stall == NO_STALL) execute_s.first_stall = `SOC.stall_cause;
          if (memory_s.valid && memory_s.first_stall == NO_STALL) memory_s.first_stall = `SOC.stall_cause;
          if (writeback_s.valid && writeback_s.first_stall == NO_STALL) writeback_s.first_stall = `SOC.stall_cause;
        end
      end

      // ----------------------------------------------------------------------
      // 4) FETCH ENTER
      // ----------------------------------------------------------------------
      fetch_valid_int = `SOC.i_fetch.fetch_valid;
      fetch_buf_valid = `SOC.i_fetch.buff_res.valid;

      fetch_enter = adv_front && !flush_fe && fetch_valid_int && fetch_buf_valid;

      if (fetch_enter) begin
        automatic integer fid = next_id++;
        string            g_str;

        log_issue(fid);
        log_line_pc_inst(fid, `SOC.i_fetch.pc_o, `SOC.i_fetch.inst_o);

        // Instr grup etiketi (tek seferlik, issue sırasında)
        g_str = instr_group(`SOC.i_fetch.instr_type_o);
        if (fd != 0) $fwrite(fd, "L\t%0d\t1\tgrp=%s\n", fid, g_str);

        log_stage_start(fid, "F");

        fetch_s <= '{
            id              : fid,
            pc              : `SOC.i_fetch.pc_o,
            inst            : `SOC.i_fetch.inst_o,
            valid           : 1'b1,
            started_f       : 1'b1,
            started_d       : 1'b0,
            started_x       : 1'b0,
            started_m       : 1'b0,
            started_wb      : 1'b0,
            instr_type      : `SOC.i_fetch.instr_type_o,
            stall_cycles    : 0,
            mem_stall_cycles: 0,
            first_stall     : NO_STALL,
            retired         : 1'b0
        };
      end else if (adv_front) begin
        // Front ilerliyor ama yeni fetch yok: bubble
        fetch_s <= '{first_stall: NO_STALL, instr_type: Null_Instr_Type, default: 0};
      end
      // Front stall/flush durumunda fetch_s olduğu gibi kalır

      // ----------------------------------------------------------------------
      // 5) Bu cycle'da hangi stage'e giriş var? (enter_now)
      //     - D: prev_fetch → decode
      //     - X: prev_decode → execute
      //     - M: prev_execute → memory
      //     - Wb: prev_memory → writeback
      // ----------------------------------------------------------------------
      d_enter_now  = (!flush_fe && adv_front && prev_fetch.valid);
      x_enter_now  = (!flush_fe && adv_back && prev_decode.valid);
      m_enter_now  = (!flush_fe && adv_back && prev_execute.valid);
      wb_enter_now = (!flush_fe && adv_back && prev_memory.valid);

      if (d_enter_now) log_stage_start(prev_fetch.id, "D");
      if (x_enter_now) log_stage_start(prev_decode.id, "X");
      if (m_enter_now) log_stage_start(prev_execute.id, "M");
      if (wb_enter_now) log_stage_start(prev_memory.id, "Wb");

      // ----------------------------------------------------------------------
      // 6) Stage EXIT + RETIRE / FLUSH
      // ----------------------------------------------------------------------
      if (flush_fe) begin
        // Flush: tüm yaşayanlar R flush
        if (prev_fetch.valid) log_retire_flush(prev_fetch.id);
        if (prev_decode.valid) log_retire_flush(prev_decode.id);
        if (prev_execute.valid) log_retire_flush(prev_execute.id);
        if (prev_memory.valid) log_retire_flush(prev_memory.id);
        if (prev_writeback.valid) begin
          log_retire_flush(prev_writeback.id);
          wb_closed = 1'b1;
        end
      end else begin
        // Normal stage kapamaları
        if (prev_fetch.valid && prev_fetch.started_f) log_stage_end(prev_fetch.id, "F");
        if (prev_decode.valid && prev_decode.started_d) log_stage_end(prev_decode.id, "D");
        if (prev_execute.valid && prev_execute.started_x) log_stage_end(prev_execute.id, "X");
        if (prev_memory.valid && prev_memory.started_m) log_stage_end(prev_memory.id, "M");

        // WB: E + R + metadata
        //  - retired flag'i ile aynı instr için tekrar tekrar R yazmayı engelliyoruz
        if (prev_writeback.valid && prev_writeback.started_wb && !prev_writeback.retired) begin
          string g_str, st_str;
          int mem_lat;

          g_str   = instr_group(prev_writeback.instr_type);
          st_str  = stall_to_str(prev_writeback.first_stall);
          mem_lat = prev_writeback.mem_stall_cycles;

          // Metadata satırı:
          //   grp=..., stall=..., stall_cycles=N [mem_latency=M]
          if (fd != 0) begin
            $fwrite(fd, "L\t%0d\t1\tgrp=%s stall=%s stall_cycles=%0d", prev_writeback.id, g_str, st_str, prev_writeback.stall_cycles);
            if (mem_lat > 0) $fwrite(fd, " mem_latency=%0d", mem_lat);
            $fwrite(fd, "\n");
          end

          // Wb stage close + retire
          log_stage_end(prev_writeback.id, "Wb");
          log_retire(prev_writeback.id);
          wb_closed = 1'b1;

          // Bu instr artık retire edildi, bir daha R yazma
          writeback_s.retired <= 1'b1;
        end
      end

      // ----------------------------------------------------------------------
      // 7) PIPELINE SHIFT
      // ----------------------------------------------------------------------
      if (flush_fe) begin
        // Flush'ta hepsini boşalt
        fetch_s     <= '{first_stall: NO_STALL, instr_type: Null_Instr_Type, default: 0};
        decode_s    <= '{first_stall: NO_STALL, instr_type: Null_Instr_Type, default: 0};
        execute_s   <= '{first_stall: NO_STALL, instr_type: Null_Instr_Type, default: 0};
        memory_s    <= '{first_stall: NO_STALL, instr_type: Null_Instr_Type, default: 0};
        writeback_s <= '{first_stall: NO_STALL, instr_type: Null_Instr_Type, default: 0};
      end else begin
        // Back (X/M/Wb) sadece adv_back olduğunda kayıyor
        if (adv_back) begin
          writeback_s <= prev_memory;
          memory_s    <= prev_execute;
          execute_s   <= prev_decode;

          if (x_enter_now) execute_s.started_x <= 1'b1;
          if (m_enter_now) memory_s.started_m <= 1'b1;
          if (wb_enter_now) writeback_s.started_wb <= 1'b1;
        end

        // Front (D) sadece adv_front olduğunda kayıyor
        if (adv_front) begin
          decode_s <= prev_fetch;
          if (d_enter_now) decode_s.started_d <= 1'b1;
        end
      end

      // ----------------------------------------------------------------------
      // 8) cycle++
      // ----------------------------------------------------------------------
      cycle_cnt <= cycle_cnt + 1;
    end
  end

  // ----------------------------------------------------------------------------
  // close
  // ----------------------------------------------------------------------------
  final begin
    if (fd != 0) begin
      $display("✅ [konata_logger] File: %s  Cycles: %0d", log_path, cycle_cnt);
      $fclose(fd);
    end
  end

endmodule

`endif  // KONATA_TRACER
`endif  // KONATA_TRACER
