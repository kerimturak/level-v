// ============================================================================
// Level RISC-V — Commit (Writeback) Gözlem Arayüzü
// ----------------------------------------------------------------------------
// "Beyaz kutu" gözlem noktası: bu interface, tb_top içinde `bind cpu ...`
// ile çekirdeğin İÇİNE enjekte edilir. Bind port bağlantıları cpu.sv'nin
// dahili sinyallerine (pipe4.*, wb_rf_rw, wb_data) doğrudan erişir; RTL'de
// tek satır değişiklik gerektirmez — ileri düzey UVM tekniklerinden
// "bind ile pasif gözlem" budur.
//
// Not: COMMIT_TRACER makrosu kapalıyken pipe4 içinde PC alanı yoktur;
// bu yüzden pc_incr (PC + 2/4) gözlenir. Register yazan her emeklilik
// (retire) için: rf_we && rd_addr/rd_wdata geçerli.
//
// Kullanım amaçları:
//   * Watchdog: çekirdek N çevrim boyunca hiç commit etmiyorsa kilitlenme.
//   * Coverage: rd dağılımı, yazılan veri uçları.
//   * Commit trace dosyası: offline Spike karşılaştırması için kayıt.
// ============================================================================
`timescale 1ns / 1ps

interface commit_if (
    input logic        clk,
    input logic        rst_n,
    input logic        rf_we,     // Bu çevrimde register dosyasına yazma var
    input logic [ 4:0] rd_addr,   // Yazılan register (x0..x31)
    input logic [31:0] rd_wdata,  // Yazılan değer (WB mux çıkışı)
    input logic [31:0] pc_incr    // Emekli olan komutun PC+4 (veya +2) değeri
);

  // Monitör yalnızca örnekler; hiçbir sinyal sürülmez (tamamen pasif).
  clocking mon_cb @(posedge clk);
    default input #1step;
    input rf_we, rd_addr, rd_wdata, pc_incr;
  endclocking

  modport MON (clocking mon_cb, input clk, rst_n);

endinterface : commit_if
