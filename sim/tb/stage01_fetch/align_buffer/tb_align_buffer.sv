`timescale 1ns / 1ps

import ceres_param::*;


module tb_align_buffer;

  // Clock, reset ve flush sinyalleri
  logic       clk;
  logic       rst_n;
  logic       flush;

  // DUT için giriş/çıkış sinyalleri
  abuff_req_t buff_req;
  abuff_res_t buff_res;
  blowX_res_t lowX_res;
  blowX_req_t lowX_req;

  // DUT instance'ı
  align_buffer #(
      .CACHE_SIZE(256),  // Örnek değer; BUFFER_CAPACITY'ye uygun
      .BLK_SIZE  (128),
      .XLEN      (32),
      .NUM_WAY   (1),
      .DATA_WIDTH(16)
  ) dut (
      .clk_i     (clk),
      .rst_ni    (rst_n),
      .flush_i   (flush),
      .buff_req_i(buff_req),
      .buff_res_o(buff_res),
      .lowX_res_i(lowX_res),
      .lowX_req_o(lowX_req)
  );

  // Clock üretimi: 10 ns periyot
  always #5 clk = ~clk;

  // LowX yanıtını bir cycle gecikmeli sağlamak için yardımcı sinyal
  // Bu blok, buff_req.valid sinyaline bağlı olarak lowX_res'in
  // bir sonraki clock cycle'da aktif hale gelmesini sağlar.
  logic lowX_response_pending;
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) lowX_response_pending <= 0;
    else
      // buff_req.valid anında değil, bir sonraki cycle'da yanıt üretecek
      lowX_response_pending <= buff_req.valid;
  end

  // LowX_res sinyalini sürmek: Eğer lowX_response_pending aktifse,
  // gelen buff_req.addr değerine göre farklı veri blokları sağlanır.
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      lowX_res <= '{valid: 0, ready: 0, blk: 128'h0};
    end else begin
      if (lowX_response_pending) begin
        // Örnek: Farklı adres değerlerine göre yanıt veriliyor.
        if (buff_req.addr == 32'h0000_0010) begin
          lowX_res <= '{valid: 1, ready: 0, blk: 128'hAAAA_BBBB_CCCC_DDDD_EEEE_FFFF_1111_2222};
        end else if (buff_req.addr == 32'h0000_00F8) begin
          lowX_res <= '{valid: 1, ready: 0, blk: 128'hDEAD_BEEF_DEAD_BEEF_DEAD_BEEF_DEAD_BEEF};
        end else if (buff_req.uncached) begin
          lowX_res <= '{valid: 0, ready: 0, blk: 128'h0};  // Uncached durumlarda yanıt verilmez
        end else begin
          lowX_res <= '{valid: 1, ready: 0, blk: 128'h1234_5678_9ABC_DEF0_1234_5678_9ABC_DEF0};
        end
      end else begin
        lowX_res <= '{valid: 0, ready: 0, blk: 128'h0};
      end
    end
  end

  // Stimulus (uyarı) üretimi
  initial begin
    // Başlangıç değerleri
    clk      = 0;
    rst_n    = 0;
    flush    = 0;
    buff_req = '{valid: 0, ready: 1, uncached: 0, addr: 32'h0};

    // Reset uygulaması
    #20;
    rst_n = 1;
    #10;

    // Senaryo 1: Aligned erişim
    // Adresin cache satır sınırlarına uygun olduğu durumda:
    // BOFFSET = $clog2(128/8)=4, dolayısıyla addr[3:0] = 4'b0000
    buff_req = '{valid: 1, ready: 1, uncached: 0, addr: 32'h0000_0010};
    #10;  // buff_req valid; lowX_res, bir sonraki cycle'da üretilecek.
    #20;
    buff_req.valid = 0;
    #20;

    // Senaryo 2: Unaligned erişim
    // Unaligned durum: addr[BOFFSET-1:1] tümü 1 (örneğin, BOFFSET=4, addr[3:1]=3'b111)
    buff_req = '{valid: 1, ready: 1, uncached: 0, addr: 32'h0000_00F8};
    #10;
    #20;
    buff_req.valid = 0;
    #20;

    // Senaryo 3: Uncached erişim (lowX_res sinyali geç verilmekte / verilmez)
    buff_req = '{valid: 1, ready: 1, uncached: 1, addr: 32'h0000_0100};
    #10;
    #20;
    buff_req.valid = 0;
    #20;

    // Senaryo 4: Flush sinyali aktif
    flush = 1;
    #10;
    flush = 0;
    #20;

    // Sonlandırma
    #50;
    $stop;
  end

  // İzleme (opsiyonel)
  initial begin
    $display("Time\tclk\trst_n\tflush\tbuff_req.addr\tbuff_req.valid\tbuff_res.blk\tbuff_res.valid\tbuff_res.miss");
    $monitor("%0t\t%b\t%b\t%b\t%h\t%b\t%h\t%b\t%b", $time, clk, rst_n, flush, buff_req.addr, buff_req.valid, buff_res.blk, buff_res.valid, buff_res.miss);
  end

endmodule
