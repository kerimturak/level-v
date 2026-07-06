// ============================================================================
// Level RISC-V UVM — Seyrek (Sparse) Bellek Modeli
// ----------------------------------------------------------------------------
// 4 GB adres uzayının tamamını temsil eden, byte adresli, associative-array
// tabanlı bellek. Yalnızca dokunulan byte'lar saklanır; bu sayede rastgele
// programlar RAM/CLINT/periferik bölgelerine serbestçe erişebilir.
//
// Backdoor API:
//   * write8/16/32, read8/32, write_line/read_line — sequence/scoreboard için
//   * load_hex_file  — riscv-dv / riscv-tests üretimi .hex imajları yükler
//   * Dokunulmamış adresler deterministik bir "boyama" değeri döndürür;
//     böylece başlatılmamış okuma kaynaklı X yayılımı olmaz ve hatalar
//     tekrarlanabilir kalır.
//
// uvm_object'ten türetilmiştir (component değil): factory ile override
// edilebilir, config_db üzerinden agent/sequence/scoreboard arasında
// TEK referans olarak paylaşılır — herkes aynı belleği görür.
// ============================================================================

class mem_model extends uvm_object;

  `uvm_object_utils(mem_model)

  // Byte adresli seyrek depo. Anahtar: 32-bit adres, değer: 1 byte.
  protected bit [7:0] mem[bit [31:0]];

  // Dokunulmamış byte'lar için boyama deseni. Adresten türetilir ki
  // aynı adres her okunduğunda aynı değer dönsün (tekrarlanabilirlik).
  bit use_addr_paint = 1;      // 0 -> sabit poison değeri döner
  bit [7:0] poison   = 8'hA5;  // use_addr_paint=0 iken dönen sabit

  function new(string name = "mem_model");
    super.new(name);
  endfunction

  // --------------------------------------------------------------------------
  // Temel byte erişimleri
  // --------------------------------------------------------------------------
  function bit [7:0] read8(bit [31:0] addr);
    if (mem.exists(addr)) return mem[addr];
    // Boyama: adresin byte'larının XOR'u — ucuz ama adrese özgü desen.
    return use_addr_paint ? (addr[7:0] ^ addr[15:8] ^ addr[23:16] ^ 8'h5A)
                          : poison;
  endfunction

  function void write8(bit [31:0] addr, bit [7:0] data);
    mem[addr] = data;
  endfunction

  // --------------------------------------------------------------------------
  // Word / half yardımcıları (little-endian)
  // --------------------------------------------------------------------------
  function bit [31:0] read32(bit [31:0] addr);
    return {read8(addr + 3), read8(addr + 2), read8(addr + 1), read8(addr)};
  endfunction

  function void write32(bit [31:0] addr, bit [31:0] data);
    for (int i = 0; i < 4; i++) write8(addr + i, data[8*i +: 8]);
  endfunction

  function void write16(bit [31:0] addr, bit [15:0] data);
    for (int i = 0; i < 2; i++) write8(addr + i, data[8*i +: 8]);
  endfunction

  // --------------------------------------------------------------------------
  // Cache satırı (16B) erişimleri — iomem responder'ın ana yolu
  // --------------------------------------------------------------------------
  // Satır okuması: addr'nin 16B hizalı tabanından 16 byte döner.
  function bit [LV_BLK_BITS-1:0] read_line(bit [31:0] addr);
    bit [31:0] base = {addr[31:4], 4'h0};
    bit [LV_BLK_BITS-1:0] line;
    for (int i = 0; i < LV_BLK_BYTES; i++) line[8*i +: 8] = read8(base + i);
    return line;
  endfunction

  // Strobe'lu satır yazması: rw[i]=1 olan byte'lar pozisyonel yazılır.
  // Cached eviction (rw='1, tam satır) ve kısmi satır yazmaları kapsar.
  function void write_line(bit [31:0] addr, bit [LV_BLK_BITS-1:0] data,
                           bit [15:0] strb);
    bit [31:0] base = {addr[31:4], 4'h0};
    for (int i = 0; i < LV_BLK_BYTES; i++)
      if (strb[i]) write8(base + i, data[8*i +: 8]);
  endfunction

  // Uncached yazma: RTL sözleşmesi gereği yazılacak word data[31:0]'dadır,
  // strobe'lar ise satır içi pozisyondadır (addr[3:0] kadar kaymış).
  // Word içi byte seçimi strobe'un word dilimiyle yapılır.
  function void write_uncached(bit [31:0] addr, bit [31:0] wword,
                               bit [15:0] strb);
    bit [31:0] word_base = {addr[31:2], 2'b00};
    bit [3:0]  sel       = strb >> (addr[3:2] * 4);  // word içi byte enable
    for (int i = 0; i < 4; i++)
      if (sel[i]) write8(word_base + i, wword[8*i +: 8]);
  endfunction

  // Uncached okuma: adreslenen word 4 lane'e kopyalanır
  // (wb_master_bridge'in gerçek SoC'taki davranışının aynısı).
  function bit [LV_BLK_BITS-1:0] read_uncached(bit [31:0] addr);
    bit [31:0] w = read32({addr[31:2], 2'b00});
    return {4{w}};
  endfunction

  // --------------------------------------------------------------------------
  // Program yükleme
  // --------------------------------------------------------------------------
  // Verilog .hex imajı yükler (word-per-line, $readmemh formatı).
  // base: imajın yerleşeceği bayt adresi (varsayılan reset vektörü).
  function void load_hex_file(string path, bit [31:0] base = LV_RESET_VECTOR);
    bit [31:0] img[];
    int fd, n;
    string line;
    bit [31:0] w;
    fd = $fopen(path, "r");
    if (fd == 0)
      `uvm_fatal("MEM_MODEL", $sformatf("Hex dosyasi acilamadi: %s", path))
    n = 0;
    while (!$feof(fd)) begin
      void'($fgets(line, fd));
      if (line.len() == 0) continue;
      // @adres satırları (opsiyonel) ve boş/yorum satırlarını atla
      if (line[0] == "@") begin
        void'($sscanf(line.substr(1, line.len()-1), "%h", base));
        continue;
      end
      if ($sscanf(line, "%h", w) == 1) begin
        write32(base + n*4, w);
        n++;
      end
    end
    $fclose(fd);
    `uvm_info("MEM_MODEL",
              $sformatf("%0d word yuklendi: %s (taban=0x%08h)", n, path, base),
              UVM_LOW)
  endfunction

  // Belirtilen bölgeyi rastgele byte'larla doldur (load/store veri alanı).
  function void randomize_region(bit [31:0] base, int nbytes);
    for (int i = 0; i < nbytes; i++)
      write8(base + i, $urandom_range(0, 255));
  endfunction

  function void clear();
    mem.delete();
  endfunction

  function int num_bytes();
    return mem.num();
  endfunction

endclass : mem_model
