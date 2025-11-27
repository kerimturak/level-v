/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/
integer log_file;

// Log dosyasını aç
initial begin
  log_file = $fopen("fetch_log.txt", "w");
  if (log_file == 0) begin
    $display("ERROR: Log file could not be opened!");
    $finish;
  end
end

// Fetch edilen instruction’ları kaydet
always @(posedge clk_i) begin
  if (!rst_ni) begin
    $fclose(log_file);
    log_file = $fopen("fetch_log.txt", "w");
  end else if ((stall_i == NO_STALL) && buff_res.valid) begin
    if (is_comp) begin
      // compressed instruction (16 bit)
      $fwrite(log_file, "core   0: 3 0x%08h (0x%08h)\n", pc_o, {16'b0, buff_res.blk[15:0]});
    end else begin
      // normal 32 bit instruction
      $fwrite(log_file, "core   0: 3 0x%08h (0x%08h)\n", pc_o, buff_res.blk);
    end
  end
end

// Simülasyon bittiğinde dosyayı kapat
final begin
  $fclose(log_file);
end
