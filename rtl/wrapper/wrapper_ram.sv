/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
`timescale 1ns / 1ps
module wrapper_ram #(
    parameter NB_COL           = 4,           // Sütun sayısı (byte sayısı)
    parameter COL_WIDTH        = 8,           // Her sütunun bit genişliği (byte)
    parameter RAM_DEPTH        = 131072,      // Bellek derinliği
    parameter INIT_FILE        = "",          // Başlangıç dosyası (varsa)
    parameter CPU_CLK          = 50_000_000,
    parameter PROG_BAUD_RATE   = 115200,
    // Programlama FSM parametreleri ve sinyalleri
    parameter PROGRAM_SEQUENCE = "ceresTEST"  // Beklenen programlama başlangıç dizisi

) (
    input logic clk_i,
    input logic rst_ni,
    input logic [$clog2(RAM_DEPTH)-1:0] wr_addr,
    input logic [$clog2(RAM_DEPTH)-1:0] rd_addr,
    input logic [(NB_COL*COL_WIDTH)-1:0] wr_data,
    input logic [NB_COL-1:0] wr_en,
    output logic [(NB_COL*COL_WIDTH)-1:0] rd_data,
    input logic rd_en,
    input logic ram_prog_rx_i,
    output logic system_reset_o,
    output logic prog_mode_led_o
);

  localparam PROG_SEQ_LENGTH = 9;
  localparam SEQ_BREAK_THRESHOLD = 32'd1000000;

  // Bellek tanımı
  logic [(NB_COL*COL_WIDTH)-1:0] ram                                          [0:RAM_DEPTH-1];
  logic [(NB_COL*COL_WIDTH)-1:0] ram_prog_data;
  logic                          ram_prog_data_valid;
  logic [ $clog2(RAM_DEPTH)-1:0] prog_addr;
  logic [ $clog2(RAM_DEPTH)-1:0] wr_addr_ram;
  logic [(NB_COL*COL_WIDTH)-1:0] wr_data_ram;
  logic [ PROG_SEQ_LENGTH*8-1:0] received_sequence;
  logic [                   3:0] rcv_seq_ctr;  // Dizinin alınan bayt sayacı
  logic [                  31:0] sequence_break_ctr;
  logic                          sequence_break;
  logic [                  31:0] prog_uart_do;

  // FSM durumları
  typedef enum logic [2:0] {
    SequenceWait       = 3'b000,
    SequenceReceive    = 3'b001,
    SequenceCheck      = 3'b011,
    SequenceLengthCalc = 3'b010,
    SequenceProgram    = 3'b110,
    SequenceFinish     = 3'b100
  } fsm_t;

  fsm_t state_prog, state_prog_next;

  // Diğer programlama ilgili sinyaller
  logic   [$clog2((NB_COL*COL_WIDTH)/8)-1:0] instruction_byte_ctr;  // Her kelimenin bayt sayacı
  logic   [          (NB_COL*COL_WIDTH)-1:0] prog_instruction;
  logic   [                            31:0] prog_intr_number;  // Beklenen program uzunluğu
  logic   [                            31:0] prog_intr_ctr;  // Alınan program uzunluğu
  logic                                      prog_inst_valid;
  logic                                      prog_sys_rst_n;
  logic                                      ram_prog_rd_en;

  // Bellek içeriğinin başlatılması: Dosya varsa okunur, yoksa tüm elemanlar 0'a eşitlenir.
  // ============================================
  // Dynamic memory init via +INIT_FILE plusarg
  // ============================================
  string                                     init_file;

  integer                                    fd;
  string                                     line;
  int                                        line_num;

  initial begin
    if ($value$plusargs("INIT_FILE=%s", init_file)) begin
      $display("------------------------------------------------------");
      $display("[INFO] Loading memory from file: %s", init_file);
      $display("------------------------------------------------------");

      // 1️⃣ Dosya içeriğini oku (ilk 8 satır örnek)
      fd = $fopen(init_file, "r");
      if (fd == 0) begin
        $display("[ERROR] Cannot open memory file: %s", init_file);
        $finish;
      end

      line_num = 0;
      while (!$feof(
          fd
      ) && line_num < 8) begin
        line_num++;
        void'($fgets(line, fd));
        line = line.tolower();  // opsiyonel, hexi küçük harf yapar
        $display("  [%0d] %s", line_num, line);
      end
      $fclose(fd);

      // 2️⃣ RAM yükle
      $readmemh(init_file, ram, 0, RAM_DEPTH - 1);
      $display("[INFO] Memory file successfully loaded into RAM.");
      $display("------------------------------------------------------");
    end else begin
      $display("[INFO] No INIT_FILE provided → initializing RAM to zero");
      ram = '{default: '0};
    end
  end


  // Bellek yazma seçimleri: Programlama modu aktifse UART'dan gelen veriler kullanılır
  assign wr_addr_ram = (prog_mode_led_o && ram_prog_data_valid) ? prog_addr : wr_addr;
  assign wr_data_ram = (prog_mode_led_o && ram_prog_data_valid) ? ram_prog_data : wr_data;

  // Okuma işlemi (senkron): rd_en aktifse okunan veriyi rd_data çıkışına aktar.
  always_ff @(posedge clk_i) begin
    if (rd_en) rd_data <= ram[rd_addr];
  end

  // Belleğe byte bazlı yazma işlemi: Her bayt için ayrı kontrol
  for (genvar i = 0; i < NB_COL; i = i + 1) begin : byte_write
    always_ff @(posedge clk_i) begin
      if (wr_en[i] || (prog_mode_led_o && ram_prog_data_valid)) ram[wr_addr_ram][i*COL_WIDTH+:COL_WIDTH] <= wr_data_ram[i*COL_WIDTH+:COL_WIDTH];
    end
  end

  // Programlama adres sayacı: Programlama modu aktifse artar, reset durumunda sıfırlanır.
  always_ff @(posedge clk_i) begin
    if (!rst_ni || !system_reset_o) prog_addr <= '0;
    else if (prog_mode_led_o && ram_prog_data_valid) prog_addr <= prog_addr + 1'b1;
  end

  // Word veri yeniden sıralaması: UART'dan gelen veriyi belleğe uygun hale getirir.
  for (genvar j = 0; j < (NB_COL * COL_WIDTH); j = j + 32) begin : reorder_word
    assign ram_prog_data[j+:32] = prog_instruction[127-j-:32];
  end

  assign ram_prog_data_valid = prog_inst_valid;
  assign system_reset_o      = prog_sys_rst_n;
  assign ram_prog_rd_en      = (state_prog != SequenceFinish);
  assign prog_mode_led_o     = (state_prog == SequenceProgram);
  assign sequence_break      = (sequence_break_ctr == SEQ_BREAK_THRESHOLD);

  // FSM durum kaydı
  always_ff @(posedge clk_i) begin
    if (!rst_ni) state_prog <= SequenceWait;
    else state_prog <= state_prog_next;
  end

  // FSM geçiş mantığı
  always_comb begin
    state_prog_next = state_prog;
    case (state_prog)
      SequenceWait: begin
        if (prog_uart_do != '1)  // Gelen veri "1" değilse programlama başlayabilir
          state_prog_next = SequenceReceive;
      end

      SequenceReceive: begin
        if (prog_uart_do != '1) begin
          if (rcv_seq_ctr == PROG_SEQ_LENGTH - 1) state_prog_next = SequenceCheck;
        end else if (sequence_break) begin
          state_prog_next = SequenceWait;
        end
      end

      SequenceCheck: begin
        if (received_sequence == PROGRAM_SEQUENCE) state_prog_next = SequenceLengthCalc;
        else state_prog_next = SequenceWait;
      end

      SequenceLengthCalc: begin
        if ((prog_uart_do != '1) && &instruction_byte_ctr[1:0]) state_prog_next = SequenceProgram;
      end

      SequenceProgram: begin
        if ((prog_intr_ctr == prog_intr_number) && ~&instruction_byte_ctr) state_prog_next = SequenceFinish;
      end

      SequenceFinish: begin
        state_prog_next = SequenceWait;
      end

      default: state_prog_next = SequenceWait;
    endcase
  end

  // FSM çıkış ve ilgili sayaçların güncellenmesi
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      instruction_byte_ctr <= '0;
      prog_instruction     <= '0;
      prog_intr_number     <= '0;
      prog_intr_ctr        <= '0;
      sequence_break_ctr   <= '0;
      received_sequence    <= '0;
      rcv_seq_ctr          <= '0;
      prog_inst_valid      <= 1'b0;
      prog_sys_rst_n       <= 1'b1;
    end else begin
      case (state_prog)
        SequenceWait: begin
          instruction_byte_ctr <= '0;
          prog_instruction     <= '0;
          prog_intr_number     <= '0;
          prog_intr_ctr        <= '0;
          sequence_break_ctr   <= '0;
          received_sequence    <= '0;
          rcv_seq_ctr          <= '0;
          prog_inst_valid      <= 1'b0;
          prog_sys_rst_n       <= 1'b1;
          if (prog_uart_do != '1) begin
            rcv_seq_ctr       <= rcv_seq_ctr + 1;
            received_sequence <= {received_sequence[PROG_SEQ_LENGTH*8-9:0], prog_uart_do[7:0]};
          end
        end

        SequenceReceive: begin
          if (prog_uart_do != '1) begin
            received_sequence <= {received_sequence[PROG_SEQ_LENGTH*8-9:0], prog_uart_do[7:0]};
            if (rcv_seq_ctr == PROG_SEQ_LENGTH - 1) rcv_seq_ctr <= 0;
            else rcv_seq_ctr <= rcv_seq_ctr + 1;
          end else begin
            if (sequence_break) sequence_break_ctr <= 0;
            else sequence_break_ctr <= sequence_break_ctr + 1;
          end
        end

        SequenceCheck: begin
          instruction_byte_ctr <= 0;  // Sıfırlama, program uzunluğu verilerini alacağız
        end

        SequenceLengthCalc: begin
          prog_intr_ctr <= 0;
          if (prog_uart_do != '1) begin
            prog_intr_number <= {prog_intr_number[23:0], prog_uart_do[7:0]};
            if (&instruction_byte_ctr[1:0]) instruction_byte_ctr <= 0;
            else instruction_byte_ctr <= instruction_byte_ctr + 1;
          end
        end

        SequenceProgram: begin
          if (prog_uart_do != '1) begin
            prog_instruction <= {prog_instruction[(NB_COL*COL_WIDTH-8)-1:0], prog_uart_do[7:0]};
            if (&instruction_byte_ctr) begin
              instruction_byte_ctr <= 0;
              prog_inst_valid      <= 1'b1;
            end else begin
              instruction_byte_ctr <= instruction_byte_ctr + 1;
              prog_inst_valid      <= 1'b0;
            end
            if (&instruction_byte_ctr[1:0]) prog_intr_ctr <= prog_intr_ctr + 1;
          end else begin
            prog_inst_valid <= 1'b0;
          end
        end

        SequenceFinish: begin
          prog_sys_rst_n <= 1'b0;
        end

        default: begin
          // Varsayılan durumda hiçbir işlem yapılmaz
        end
      endcase
    end
  end

  // Basit UART modülü örneği: Programlama sırasında veriyi almak için
  simpleuart #(
      .DEFAULT_DIV(CPU_CLK / PROG_BAUD_RATE)
  ) simpleuart_inst (
      .clk       (clk_i),
      .resetn    (rst_ni),
      .ser_tx    (),                // İsteğe bağlı, kullanılmıyorsa boş bırakılabilir
      .ser_rx    (ram_prog_rx_i),
      .reg_div_we(4'h0),
      .reg_div_di(32'h0),
      .reg_div_do(),
      .reg_dat_we(1'b0),
      .reg_dat_re(ram_prog_rd_en),
      .reg_dat_di(32'h0),
      .reg_dat_do(prog_uart_do)
  );

endmodule
