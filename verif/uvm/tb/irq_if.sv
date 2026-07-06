// ============================================================================
// Level RISC-V — UVM Kesme (IRQ) Arayüzü
// ----------------------------------------------------------------------------
// Çekirdeğin 3 asenkron kesme girişini (CLINT timer, CLINT software,
// PLIC external) UVM irq_agent'ına bağlar. Gerçek SoC'ta bu pinleri CLINT ve
// PLIC sürer; bu ortamda DUT yalnızca çekirdek olduğu için pinler doğrudan
// rastgeleleştirilmiş kesme dizileriyle (irq_seq_lib) sürülür.
//
// Pinler SEVİYE duyarlıdır: mip.MTIP/MSIP/MEIP doğrudan pin seviyesini izler.
// Bu yüzden driver "darbe süresi" kavramıyla çalışır: kesmeyi N çevrim yüksek
// tutar, sonra bırakır (yazılım pin'i temizleyemez, CLINT/PLIC yokken tek
// temizleme yolu pinin düşmesidir).
// ============================================================================
`timescale 1ns / 1ps

interface irq_if (
    input logic clk,
    input logic rst_n
);

  logic timer_irq;  // CLINT mtimecmp kesmesi (MTIP)
  logic sw_irq;     // CLINT yazılım kesmesi   (MSIP)
  logic ext_irq;    // PLIC harici kesme       (MEIP)

  // Sürücü clocking block'u — kesme pinleri clock kenarından sonra sürülür.
  clocking drv_cb @(posedge clk);
    default input #1step output #1ps;
    output timer_irq, sw_irq, ext_irq;
  endclocking

  // Monitör clocking block'u — pasif izleme + coverage için.
  clocking mon_cb @(posedge clk);
    default input #1step;
    input timer_irq, sw_irq, ext_irq;
  endclocking

  modport DRV (clocking drv_cb, input clk, rst_n);
  modport MON (clocking mon_cb, input clk, rst_n);

  // Reset sırasında kesme pinlerinin bilinen değerde başlaması için
  // prosedürel olmayan güvenli varsayılan: driver reset'te '0 sürer,
  // ama elaboration ile ilk sürüş arasında X kalmasın diye başlangıç değeri.
  initial begin
    timer_irq = 1'b0;
    sw_irq    = 1'b0;
    ext_irq   = 1'b0;
  end

endinterface : irq_if
