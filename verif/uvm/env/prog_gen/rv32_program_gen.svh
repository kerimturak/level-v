// ============================================================================
// Level RISC-V UVM — Rastgele Program Üreteci
// ----------------------------------------------------------------------------
// Kısıtlı-rastgele, KENDİ KENDİNİ SONLANDIRAN RV32IMC programları üretip
// paylaşılan mem_model'e backdoor yükler. Yerleşim (base = reset vektörü):
//
//   base+0x00  jal  x0, start            ; trap handler üzerinden atla
//   base+0x04  trap_handler:
//              csrrs x7, mcause, x0      ; x7 = mcause
//              blt   x7, x0, irq_path    ; mcause<0 (MSB=1) => kesme
//              slli  x7, x7, 1           ; --- istisna yolu ---
//              ori   x7, x7, 1           ; fail kodu = (mcause<<1)|1
//              sw    x7, 0(x6)           ; tohost = fail  -> test biter
//              jal   x0, 0               ; kendi üstünde döngü
//   base+0x1C  irq_path:
//              addi  x30, x30, 1         ; kesme sayacı (gözlemlenebilirlik)
//              mret                      ; kaldığı yerden devam
//   base+0x24  start:
//              <prolog>                  ; işaretçiler, mtvec, GPR init,
//                                        ;   (irq_mode) mie/mstatus.MIE
//              <N adet rastgele slot>    ; rv32_instr_item'lar
//              addi x7, x0, 1            ; --- epilog: PASS ---
//              sw   x7, 0(x6)            ; tohost = 1
//              jal  x0, 0                ; kendi üstünde döngü
//
// Sonlanma sözleşmesi: program tohost'a (UNCACHED adres!) yazar; scoreboard
// bu iomem yazmasını görüp testi bitirir. Trap handler sayesinde her
// beklenmeyen istisna da deterministik biçimde FAIL koduna dönüşür —
// rastgele test hiçbir zaman "sessizce kilitlenmez" (o durum da watchdog'a
// takılır).
//
// Sınıf uvm_object'tir: virtual sequence'lar factory ile yaratıp randomize
// eder; knob'ları test/plusarg katmanından şekillendirilir.
// ============================================================================

class rv32_program_gen extends uvm_object;

  `uvm_object_utils(rv32_program_gen)

  // ---- Knob'lar (randomize edilebilir üst-seviye ayarlar) ----
  rand int unsigned n_instrs;        // Gövde slot sayısı
  rand bit          en_compressed;   // C-çifti slotlarına izin
       bit          irq_mode = 0;    // 1 -> kesmeleri etkinleştir + say
       int unsigned max_fwd  = 8;    // Azami ileri dallanma (slot)

  // Bellek yerleşimi (testler değiştirebilir)
  bit [31:0]   base       = LV_RESET_VECTOR;
  bit [31:0]   tohost     = LV_TOHOST_DEFAULT;
  bit [31:0]   data_base  = LV_DATA_BASE_DEFAULT;
  int unsigned data_size  = LV_DATA_SIZE_DEFAULT;
  bit [31:0]   unc_base   = LV_UNC_DATA_BASE_DEFAULT;
  int unsigned unc_size   = 256;

  // Kategori ağırlıkları — rv32_instr_item'a kopyalanır.
  int unsigned w_arith_r = 20, w_arith_i = 20, w_muldiv = 10, w_lui = 5;
  int unsigned w_load = 15, w_store = 10, w_branch = 8, w_jal = 3;
  int unsigned w_csr = 3, w_fence = 2, w_cpair = 4;

  // Üretim sonrası rapor için istatistik
  int unsigned cat_hist[lv_instr_cat_e];
  int unsigned total_words;

  // "soft": vseq'in `randomize with { n_instrs == ... }` katmanı, buradaki
  // varsayılan aralıkla ÇELİŞSE bile kazanır (örn. +n_instrs=8000 plusarg'ı).
  // Soft olmasaydı randomize başarısız olurdu — ileri düzey constraint
  // katmanlamasının standart aracı.
  constraint c_defaults {
    soft n_instrs inside {[50:5000]};
    soft en_compressed dist { 1 :/ 70, 0 :/ 30 };
  }

  function new(string name = "rv32_program_gen");
    super.new(name);
  endfunction

  // --------------------------------------------------------------------------
  // Sabit yapı taşları — okunabilirlik için isimli kısayollar.
  // (Kodlayıcılar rv32_instr_item'ın statik fonksiyonlarıdır.)
  // --------------------------------------------------------------------------
  // li rd, imm32  ->  lui rd, hi20 ; addi rd, rd, lo12  (2 word)
  // DİKKAT: SV'de yön belirteci (ref) sonraki argümanlara da yapışır;
  // rd/imm'in ref olmaması için `input` açıkça yazılmıştır.
  protected function void emit_li(mem_model m, ref bit [31:0] pc,
                                  input bit [4:0] rd, input bit [31:0] imm);
    bit [19:0] hi = imm[31:12] + {19'b0, imm[11]};  // addi işaret düzeltmesi
    m.write32(pc, rv32_instr_item::enc_u(hi, rd, 7'b0110111));          pc += 4;
    m.write32(pc, rv32_instr_item::enc_i(imm[11:0], rd, 3'h0, rd,
                                         7'b0010011));                   pc += 4;
  endfunction

  protected function void emit(mem_model m, ref bit [31:0] pc,
                               input bit [31:0] w);
    m.write32(pc, w);
    pc += 4;
  endfunction

  // --------------------------------------------------------------------------
  // Ana giriş: programı üret ve mem_model'e yaz. Dönüş: toplam bayt.
  // --------------------------------------------------------------------------
  function int unsigned build(mem_model m);
    bit [31:0] pc;
    bit [31:0] start_pc;
    bit [31:0] handler = base + 32'h4;
    rv32_instr_item it;

    cat_hist.delete();

    // ---- Trap handler (adresler sınıf başlığındaki haritayla birebir) ----
    pc = base + 32'h4;
    emit(m, pc, rv32_instr_item::enc_i(12'h342, 5'd0, 3'h2, 5'd7,
                                       7'b1110011));            // csrrs x7,mcause,x0
    emit(m, pc, rv32_instr_item::enc_b(13'h014, 5'd0, 5'd7, 3'h4)); // blt x7,x0,+0x14
    emit(m, pc, rv32_instr_item::enc_i({7'b0, 5'd1}, 5'd7, 3'h1, 5'd7,
                                       7'b0010011));            // slli x7,x7,1
    emit(m, pc, rv32_instr_item::enc_i(12'h001, 5'd7, 3'h6, 5'd7,
                                       7'b0010011));            // ori  x7,x7,1
    emit(m, pc, rv32_instr_item::enc_s(12'h000, 5'd7, 5'd6, 3'h2)); // sw x7,0(x6)
    emit(m, pc, rv32_instr_item::enc_j(21'h0, 5'd0));           // jal x0,0 (fail loop)
    emit(m, pc, rv32_instr_item::enc_i(12'h001, 5'd30, 3'h0, 5'd30,
                                       7'b0010011));            // addi x30,x30,1
    emit(m, pc, 32'h3020_0073);                                 // mret

    // ---- Prolog ----
    start_pc = pc;  // = base + 0x24
    // base+0: handler'ın üzerinden start'a atla (geriye dönük yazılır).
    m.write32(base, rv32_instr_item::enc_j(21'(start_pc - base), 5'd0));

    emit_li(m, pc, 5'd6,  tohost);       // x6  = tohost işaretçisi
    emit_li(m, pc, 5'd7,  handler);      // x7  = handler adresi
    emit(m, pc, rv32_instr_item::enc_i(12'h305, 5'd7, 3'h1, 5'd0,
                                       7'b1110011));  // csrrw x0, mtvec, x7
    emit_li(m, pc, 5'd5,  data_base);    // x5  = cached veri tabanı
    emit_li(m, pc, 5'd28, unc_base);     // x28 = uncached veri tabanı
    emit(m, pc, rv32_instr_item::enc_i(12'h000, 5'd0, 3'h0, 5'd30,
                                       7'b0010011));  // x30 = 0 (kesme sayacı)

    // Ayrılmışlar hariç tüm GPR'ları rastgele değerlerle doldur:
    // gövdenin ilk komutundan itibaren anlamlı operanda sahip olsun.
    for (int r = 1; r < 32; r++) begin
      if (r inside {5, 6, 7, 28, 30}) continue;
      emit_li(m, pc, 5'(r), $urandom());
    end

    if (irq_mode) begin
      // mie = MSIE|MTIE|MEIE (0x888), sonra mstatus.MIE'yi imm ile aç.
      emit_li(m, pc, 5'd7, 32'h0000_0888);
      emit(m, pc, rv32_instr_item::enc_i(12'h304, 5'd7, 3'h1, 5'd0,
                                         7'b1110011));  // csrrw x0, mie, x7
      emit(m, pc, rv32_instr_item::enc_i(12'h300, 5'd8, 3'h6, 5'd0,
                                         7'b1110011));  // csrrsi x0,mstatus,8
    end

    // ---- Rastgele gövde ----
    for (int unsigned i = 0; i < n_instrs; i++) begin
      it = rv32_instr_item::type_id::create($sformatf("it_%0d", i));
      // Bağlam + knob kopyaları (rand olmayan alanlar)
      it.slot_idx      = i;
      it.max_slots     = n_instrs;   // hedef==n_instrs -> epilog başı
      it.max_fwd       = max_fwd;
      it.data_size     = data_size;
      it.unc_size      = unc_size;
      it.en_compressed = en_compressed;
      it.w_arith_r = w_arith_r; it.w_arith_i = w_arith_i;
      it.w_muldiv  = w_muldiv;  it.w_lui     = w_lui;
      it.w_load    = w_load;    it.w_store   = w_store;
      it.w_branch  = w_branch;  it.w_jal     = w_jal;
      it.w_csr     = w_csr;     it.w_fence   = w_fence;
      it.w_cpair   = w_cpair;

      if (!it.randomize())
        `uvm_fatal("PROG_GEN", $sformatf("Slot %0d randomize edilemedi", i))

      emit(m, pc, it.encode());
      cat_hist[it.cat]++;
      `uvm_info("PROG_GEN", it.convert2string(), UVM_FULL)
    end

    // ---- Epilog: PASS ----
    emit(m, pc, rv32_instr_item::enc_i(12'h001, 5'd0, 3'h0, 5'd7,
                                       7'b0010011));            // addi x7,x0,1
    emit(m, pc, rv32_instr_item::enc_s(12'h000, 5'd7, 5'd6, 3'h2)); // sw x7,0(x6)
    emit(m, pc, rv32_instr_item::enc_j(21'h0, 5'd0));           // jal x0,0

    total_words = (pc - base) / 4;

    // Program alanı veri alanına taşmasın — sözleşmenin sigortası.
    if (pc > data_base)
      `uvm_fatal("PROG_GEN", $sformatf(
          "Program (0x%08h) veri alanina (0x%08h) tasti; n_instrs kucult",
          pc, data_base))

    // Load'lar deterministik veri okusun diye veri alanlarını boya.
    m.randomize_region(data_base, data_size);
    m.randomize_region(unc_base, unc_size);

    print_stats();
    return pc - base;
  endfunction

  protected function void print_stats();
    string s = $sformatf(
        "Program: %0d word (govde=%0d slot, C=%s, irq_mode=%0d)\n",
        total_words, n_instrs, en_compressed ? "acik" : "kapali", irq_mode);
    foreach (cat_hist[c])
      s = {s, $sformatf("  %-16s : %0d\n", c.name(), cat_hist[c])};
    `uvm_info("PROG_GEN", s, UVM_LOW)
  endfunction

endclass : rv32_program_gen
