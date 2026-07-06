// ============================================================================
// Level RISC-V UVM — Ana Paket
// ----------------------------------------------------------------------------
// Tüm testbench sınıflarını tek derleme birimi altında toplar. Dosya sırası
// bağımlılık sırasıdır (SystemVerilog'da sınıflar kullanılmadan önce
// tanımlanmalıdır):
//
//   tipler -> bellek agent -> irq agent -> commit -> coverage/scoreboard
//   -> env cfg -> vsequencer -> env -> prog_gen -> vseq'ler -> testler
// ============================================================================
`timescale 1ns / 1ps

package level_v_uvm_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Ortak tipler ve sabitler
  `include "level_v_types.svh"

  // Bellek reaktif agent'ı
  `include "mem_agent/mem_model.svh"
  `include "mem_agent/mem_agent_cfg.svh"
  `include "mem_agent/mem_seq_item.svh"
  `include "mem_agent/mem_sequencer.svh"
  `include "mem_agent/mem_driver.svh"
  `include "mem_agent/mem_monitor.svh"
  `include "mem_agent/mem_seq_lib.svh"
  `include "mem_agent/mem_agent.svh"

  // Kesme agent'ı (tek dosyada tam agent)
  `include "irq_agent/irq_agent_pkg.svh"

  // Commit gözlemi
  `include "commit_agent/commit_monitor.svh"

  // Analiz katmanı
  `include "level_v_coverage.svh"
  `include "level_v_scoreboard.svh"

  // Ortam ve eşgüdüm
  `include "level_v_env_cfg.svh"
  `include "level_v_vsequencer.svh"
  `include "level_v_env.svh"

  // Rastgele program üretimi
  `include "prog_gen/rv32_instr_item.svh"
  `include "prog_gen/rv32_program_gen.svh"

  // Senaryolar ve testler
  // (test dosyası göreli ".." ile DEĞİL, +incdir+verif/uvm/tests üzerinden
  //  bulunur — vlog göreli include'ları dosya konumuna göre çözmez)
  `include "seq_lib/level_v_vseq_lib.svh"
  `include "level_v_test_lib.svh"

endpackage : level_v_uvm_pkg
