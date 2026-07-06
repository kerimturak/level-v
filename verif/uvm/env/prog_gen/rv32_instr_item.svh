// ============================================================================
// Level RISC-V UVM — Kısıtlı-Rastgele RV32IMC Komut Öğesi
// ----------------------------------------------------------------------------
// Rastgele programın GÖVDESİNDEKİ tek bir 32-bit "slot"u temsil eder.
// Her slot ya bir adet 32-bit komut ya da (en_compressed açıksa) iki adet
// 16-bit sıkıştırılmış komuttur — böylece tüm dallanma hedefleri 4 bayt
// hizalı slot sınırlarına denk gelir ve hedef hesapları güvenli kalır.
//
// GÜVENLİ RASTGELELİK SÖZLEŞMESİ (constraint'lerin var olma nedeni):
//   * rd, ayrılmış register'lara yazamaz:
//       x5  = cached veri taban işaretçisi
//       x6  = tohost işaretçisi
//       x7  = trap handler geçici register'ı
//       x28 = uncached veri taban işaretçisi
//       x30 = kesme sayacı (irq_mode)
//   * Load/store taban register'ı DAİMA x5 (cached) veya x28 (uncached);
//     ofset bölge sınırları içinde ve erişim boyutuna hizalı ->
//     hizasızlık istisnası (bilerek) üretilmez, program alanı ezilmez.
//   * Dallanma/JAL yalnızca İLERİYE, en fazla max_fwd slot; hedef gövde
//     içinde veya tam epilog başında -> sonsuz döngü imkânsız.
//   * CSR komutları yalnızca mscratch(0x340) kullanır -> yan etkisiz.
//   * ecall/ebreak üretilmez; beklenmeyen HER istisna trap handler'da
//     FAIL koduna dönüşür (bkz. rv32_program_gen).
//
// Kategori ağırlıkları rand DEĞİLDİR: üreteç cfg'sinden atanır, "dist"
// constraint'i içinde kullanılır -> testler karışımı knob'la şekillendirir.
// ============================================================================

// Komut kategorileri
typedef enum int {
  LV_CAT_ARITH_R,   // OP     : add/sub/sll/slt/sltu/xor/srl/sra/or/and
  LV_CAT_ARITH_I,   // OP-IMM : addi/slti/.../slli/srli/srai
  LV_CAT_MULDIV,    // M uzantısı: mul/mulh/.../div/rem
  LV_CAT_LUI_AUIPC, // U-tipi
  LV_CAT_LOAD,      // lb/lh/lw/lbu/lhu (x5 veya x28 tabanlı)
  LV_CAT_STORE,     // sb/sh/sw        (x5 veya x28 tabanlı)
  LV_CAT_BRANCH,    // beq/bne/blt/bge/bltu/bgeu (ileri)
  LV_CAT_JAL,       // jal x0 (ileri)
  LV_CAT_CSR,       // csrr* mscratch
  LV_CAT_FENCE,     // fence / fence.i
  LV_CAT_CPAIR      // iki adet 16-bit C komutu (c.addi/c.li/c.mv/c.nop)
} lv_instr_cat_e;

class rv32_instr_item extends uvm_object;

  `uvm_object_utils(rv32_instr_item)

  // ---- Bağlam (rand değil — üreteç randomize'dan önce doldurur) ----
  int unsigned slot_idx;        // Gövde içindeki slot numarası (0 tabanlı)
  int unsigned max_slots;       // Gövde slot sayısı (hedef==max_slots -> epilog)
  int unsigned max_fwd = 8;     // Azami ileri dallanma mesafesi (slot)
  int unsigned data_size = LV_DATA_SIZE_DEFAULT;  // cached veri alanı (bayt)
  int unsigned unc_size  = 256;                   // uncached veri alanı (bayt)
  bit          en_compressed = 1;                 // C-çifti kategorisine izin

  // Kategori ağırlıkları (dist için; 0 -> kategori kapalı)
  int unsigned w_arith_r  = 20;
  int unsigned w_arith_i  = 20;
  int unsigned w_muldiv   = 10;
  int unsigned w_lui      = 5;
  int unsigned w_load     = 15;
  int unsigned w_store    = 10;
  int unsigned w_branch   = 8;
  int unsigned w_jal      = 3;
  int unsigned w_csr      = 3;
  int unsigned w_fence    = 2;
  int unsigned w_cpair    = 4;

  // ---- Rastgele alanlar ----
  rand lv_instr_cat_e cat;
  rand bit [4:0]  rd, rs1, rs2;
  rand bit [2:0]  funct3;
  rand bit        alt;          // SUB/SRA/SRAI seçici (funct7[5])
  rand bit [4:0]  shamt;
  rand bit [11:0] imm12;
  rand bit [19:0] imm20;
  rand bit        is_unc;       // load/store: uncached bölge mi?
  rand bit [11:0] mem_off;      // load/store ofseti (pozitif)
  rand int unsigned br_slots;   // dallanma/JAL ileri slot sayısı
  rand bit        fence_i;      // 1 -> fence.i, 0 -> fence
  // C-çifti alanları
  rand bit [1:0]  c_kind0, c_kind1;  // 0:c.nop 1:c.addi 2:c.li 3:c.mv
  rand bit [5:0]  c_imm0,  c_imm1;
  rand bit [4:0]  c_rd0,   c_rd1, c_rs0, c_rs1n;

  // Ayrılmış register kümesi — rd bunlara yazamaz.
  // (x0'a yazmaya nadiren izin verilir: mimari NOP, yine de kapsanmalı.)
  constraint c_rd_reserved {
    !(rd inside {5, 6, 7, 28, 30});
    rd dist { 0 :/ 2, [1:31] :/ 98 };
  }

  // C-çifti rd'leri de aynı kurala uyar; c.addi/c.li/c.mv rd!=0 ister.
  constraint c_cpair_regs {
    !(c_rd0 inside {0, 5, 6, 7, 28, 30});
    !(c_rd1 inside {0, 5, 6, 7, 28, 30});
    c_rs0  != 0;   // c.mv rs2 != 0 zorunlu
    c_rs1n != 0;
    c_imm0 != 0;   // c.addi imm != 0 (imm==0 kodlaması hint/rezerve)
    c_imm1 != 0;
  }

  // Kategori dağılımı — ağırlıklar knob.
  constraint c_cat {
    cat dist {
      LV_CAT_ARITH_R   :/ w_arith_r,
      LV_CAT_ARITH_I   :/ w_arith_i,
      LV_CAT_MULDIV    :/ w_muldiv,
      LV_CAT_LUI_AUIPC :/ w_lui,
      LV_CAT_LOAD      :/ w_load,
      LV_CAT_STORE     :/ w_store,
      LV_CAT_BRANCH    :/ w_branch,
      LV_CAT_JAL       :/ w_jal,
      LV_CAT_CSR       :/ w_csr,
      LV_CAT_FENCE     :/ w_fence,
      LV_CAT_CPAIR     :/ (en_compressed ? w_cpair : 0)
    };
  }

  // funct3, kategoriye göre geçerli değer kümesinden seçilir.
  constraint c_funct3 {
    (cat == LV_CAT_LOAD)   -> funct3 inside {3'h0, 3'h1, 3'h2, 3'h4, 3'h5};
    (cat == LV_CAT_STORE)  -> funct3 inside {3'h0, 3'h1, 3'h2};
    (cat == LV_CAT_BRANCH) -> funct3 inside {3'h0, 3'h1, 3'h4, 3'h5, 3'h6, 3'h7};
    (cat == LV_CAT_CSR)    -> funct3 inside {3'h1, 3'h2, 3'h3, 3'h5, 3'h6, 3'h7};
    // OP/OP-IMM/M için 0..7 tamamı geçerli (alt bit ayrıca kısıtlanır)
  }

  // SUB/SRA yalnızca funct3 0/5'te anlamlı; diğerlerinde alt=0 olmalı.
  constraint c_alt {
    (cat == LV_CAT_ARITH_R && !(funct3 inside {3'h0, 3'h5})) -> (alt == 0);
    (cat == LV_CAT_ARITH_I && funct3 != 3'h5)                -> (alt == 0);
  }

  // Load/store ofseti: bölge içinde ve erişim boyutuna hizalı.
  // (funct3[1:0]: 0=byte, 1=half, 2=word — hizalama maskesi ile)
  constraint c_mem {
    solve is_unc, funct3 before mem_off;
    is_unc dist { 0 :/ 80, 1 :/ 20 };
    if (is_unc) {
      mem_off < unc_size;
    } else {
      mem_off < data_size;
    }
    (funct3[1:0] == 2'h1) -> (mem_off[0]   == 1'b0);  // half hizası
    (funct3[1:0] == 2'h2) -> (mem_off[1:0] == 2'b00); // word hizası
  }

  // Dallanma hedefi: ileri, sınır içinde. (max_slots'a eşit hedef = epilog)
  constraint c_branch {
    br_slots >= 1;
    br_slots <= max_fwd;
    slot_idx + br_slots <= max_slots;
  }

  function new(string name = "rv32_instr_item");
    super.new(name);
  endfunction

  // --------------------------------------------------------------------------
  // Kodlayıcı (mini assembler) — randomize edilmiş alanlardan 32-bit word.
  // Statik yardımcılar rv32_program_gen tarafından da kullanılır.
  // --------------------------------------------------------------------------
  static function bit [31:0] enc_r(bit [6:0] f7, bit [4:0] rs2, bit [4:0] rs1,
                                   bit [2:0] f3, bit [4:0] rd, bit [6:0] op);
    return {f7, rs2, rs1, f3, rd, op};
  endfunction

  static function bit [31:0] enc_i(bit [11:0] imm, bit [4:0] rs1,
                                   bit [2:0] f3, bit [4:0] rd, bit [6:0] op);
    return {imm, rs1, f3, rd, op};
  endfunction

  static function bit [31:0] enc_s(bit [11:0] imm, bit [4:0] rs2,
                                   bit [4:0] rs1, bit [2:0] f3);
    return {imm[11:5], rs2, rs1, f3, imm[4:0], 7'b0100011};
  endfunction

  static function bit [31:0] enc_b(bit [12:0] imm, bit [4:0] rs2,
                                   bit [4:0] rs1, bit [2:0] f3);
    return {imm[12], imm[10:5], rs2, rs1, f3, imm[4:1], imm[11], 7'b1100011};
  endfunction

  static function bit [31:0] enc_u(bit [19:0] imm, bit [4:0] rd, bit [6:0] op);
    return {imm, rd, op};
  endfunction

  static function bit [31:0] enc_j(bit [20:0] imm, bit [4:0] rd);
    return {imm[20], imm[10:1], imm[11], imm[19:12], rd, 7'b1101111};
  endfunction

  // 16-bit C komutu kodlayıcıları
  static function bit [15:0] enc_c_addi(bit [4:0] rd, bit [5:0] imm);
    return {3'b000, imm[5], rd, imm[4:0], 2'b01};
  endfunction

  static function bit [15:0] enc_c_li(bit [4:0] rd, bit [5:0] imm);
    return {3'b010, imm[5], rd, imm[4:0], 2'b01};
  endfunction

  static function bit [15:0] enc_c_mv(bit [4:0] rd, bit [4:0] rs2);
    return {4'b1000, rd, rs2, 2'b10};
  endfunction

  static function bit [15:0] enc_c_nop();
    return 16'h0001;
  endfunction

  // Tek C komutu üret (c_kind koduna göre)
  protected function bit [15:0] enc_c_one(bit [1:0] kind, bit [4:0] rd_,
                                          bit [4:0] rs_, bit [5:0] imm_);
    case (kind)
      2'd1:    return enc_c_addi(rd_, imm_);
      2'd2:    return enc_c_li(rd_, imm_);
      2'd3:    return enc_c_mv(rd_, rs_);
      default: return enc_c_nop();
    endcase
  endfunction

  // Randomize edilmiş öğeyi 32-bit makine koduna çevir.
  function bit [31:0] encode();
    case (cat)
      LV_CAT_ARITH_R:
        return enc_r({1'b0, alt, 5'b0}, rs2, rs1, funct3, rd, 7'b0110011);

      LV_CAT_ARITH_I: begin
        if (funct3 == 3'h1)       // slli
          return enc_i({7'b0000000, shamt}, rs1, funct3, rd, 7'b0010011);
        else if (funct3 == 3'h5)  // srli/srai
          return enc_i({1'b0, alt, 5'b0, shamt}, rs1, funct3, rd, 7'b0010011);
        else
          return enc_i(imm12, rs1, funct3, rd, 7'b0010011);
      end

      LV_CAT_MULDIV:
        return enc_r(7'b0000001, rs2, rs1, funct3, rd, 7'b0110011);

      LV_CAT_LUI_AUIPC:
        // alt biti LUI/AUIPC seçici olarak yeniden kullanılır
        return enc_u(imm20, rd, alt ? 7'b0010111 : 7'b0110111);

      LV_CAT_LOAD:
        // Taban: x5 (cached) veya x28 (uncached) — sözleşmenin kalbi.
        return enc_i(mem_off, is_unc ? 5'd28 : 5'd5, funct3, rd, 7'b0000011);

      LV_CAT_STORE:
        return enc_s(mem_off, rs2, is_unc ? 5'd28 : 5'd5, funct3);

      LV_CAT_BRANCH:
        // Hedef ofseti: slot cinsinden ileri mesafe * 4 bayt.
        return enc_b(13'(br_slots * 4), rs2, rs1, funct3);

      LV_CAT_JAL:
        // rd=x0: link kaydetme — kontrol akışı sözleşmesi bozulmasın.
        return enc_j(21'(br_slots * 4), 5'd0);

      LV_CAT_CSR: begin
        // Yalnızca mscratch(0x340): yan etkisiz oyun alanı.
        // Immediate türevlerde rs1 alanı uimm5'tir.
        return enc_i(12'h340, funct3[2] ? {2'b0, imm12[2:0]} : rs1,
                     funct3, rd, 7'b1110011);
      end

      LV_CAT_FENCE:
        return fence_i ? 32'h0000100F   // fence.i (icache flush yolu!)
                       : 32'h0FF0000F;  // fence iorw,iorw

      LV_CAT_CPAIR:
        // Little-endian: düşük yarım-word düşük adreste yürütülür.
        return {enc_c_one(c_kind1, c_rd1, c_rs1n, c_imm1),
                enc_c_one(c_kind0, c_rd0, c_rs0,  c_imm0)};

      default: return 32'h0000_0013;  // nop (addi x0,x0,0)
    endcase
  endfunction

  function string convert2string();
    return $sformatf("slot=%0d cat=%s rd=x%0d word=0x%08h",
                     slot_idx, cat.name(), rd, encode());
  endfunction

endclass : rv32_instr_item
