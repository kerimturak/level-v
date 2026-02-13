# 1. Giriş (Introduction)

Bu modülün amacı, RISC-V **sıkıştırılmış komutları** (compressed instructions) destekleyen bir **talimat hizalama tamponu** (instruction align buffer) tasarlamaktır.
RISC-V "C" uzantısı (C extension), sık kullanılan 32-bit komutların (32-bit instructions) bir kısmını 16-bit komutlar (16-bit instructions) ile değiştirerek program boyutunu yaklaşık %25 oranında küçültür. Ancak bu yaklaşım, **talimat getirme biriminde** (instruction fetch unit) ek karmaşıklığa neden olur. Özellikle, 32-bit ve 16-bit komutların aynı bellek alanında (instruction memory) boşluksuz (without gaps) olarak bir arada bulunması, hizalama (alignment) problemleri doğurur.

Örneğin:

* 32-bit’lik bir komut bellek içinde iki 16-bit girişe (entries) bölünebilir.
* Eğer komut 32-bit sınırına (32-bit boundary) hizalı değilse, bu komutu getirebilmek için iki farklı bellek erişimi (memory access) gerekebilir.
* Bu durum, **çevrim başına talimat** (IPC – Instructions Per Cycle) oranını düşürür.

Bu problemi çözmek için tasarlanan **hizalama tamponu** (align buffer), bellekteki her 32-bit komutu iki adet 16-bit parçaya (parcel) ayırır. Ardından, gelen **program sayacı** (Program Counter – PC) adresine göre gerekli parçaları seçer ve gerekirse iki farklı girişi (entries) birleştirerek (concatenate) nihai 32-bit komutu oluşturur.

Bu yaklaşım, literatürdeki **Gray önbellek yapısı**na (Gray cache structure) benzer bir yöntemdir. Ancak tasarım FPGA üzerinde kullanılmak üzere sadeleştirilmiş ve optimize edilmiştir. Böylece:

* **Hizalı erişimlerde** (aligned access) tek adımda doğru 32-bit komut oluşturulur.
* **Hizalı olmayan erişimlerde** (unaligned access), tampon iki banktan (even bank, odd bank) parçaları alıp birleştirerek komutu üretir.

Sonuç olarak, bu modül RISC-V sıkıştırılmış komut uzantısını destekleyen işlemcilerde, **yüksek performanslı talimat getirme** (high-performance instruction fetch) sürecini mümkün kılar.

---

## Adres Bit Ayrımı (Address Bit Breakdown)

Bir talimat adresi (instruction address) RISC-V mimarisinde **bayt adresli** (byte-addressable) olup, her adres bir baytı gösterir.
Bizim tasarımımızda **blok boyutu** (block size, `BLK_SIZE`) **128 bit = 16 bayt** olarak belirlenmiştir. Bu durumda:

* **Program Sayacı (Program Counter, PC)**: 32 bit
* **Tag Alanı (Tag field)**: Üst bitler (üst adres kısmı)
* **Index Alanı (Index field)**: Bellek setini seçmek için kullanılır
* **Block Offset (BOFFSET)**: Bloğun içindeki baytı gösterir

### Genel Formül

```
PC[31 ............... (IDX_WIDTH+BOFFSET)] = Tag
PC[(IDX_WIDTH+BOFFSET-1) .... BOFFSET]    = Index
PC[BOFFSET-1 : 0]                         = Block Offset
```

### 128-bit (16-byte) Blok Örneği

* `BLK_SIZE = 128 bit = 16 byte`
* `BOFFSET = log2(16) = 4 bit`
* Yani `PC[3:0]` bloğun içindeki offset (block offset).

Bunu açarsak:

* **PC\[1:0]** → 16-bit hizalama için parcel seçiminde kullanılır
* **PC\[3:2]** → Bloğun içindeki 32-bit kelimeyi (word) seçer
* **PC\[IDX\_WIDTH+3:4]** → Index
* **PC\[31\:IDX\_WIDTH+4]** → Tag

### Örnek

Diyelim ki:

* `CACHE_SIZE = 512 B`
* `BLK_SIZE = 16 B`
* `NUM_WAY = 1`

O zaman:

* `NUM_SET = 512 / 16 = 32` set
* `IDX_WIDTH = log2(32) = 5`
* `BOFFSET = log2(16) = 4`
* `TAG_SIZE = 32 - (5 + 4) = 23`

#### Adres Dağılımı

```
PC[31:9] = Tag (23 bit)
PC[8:4]  = Index (5 bit)
PC[3:0]  = Block Offset (4 bit)
```

#### Offset Ayrıntısı

* PC\[3:2] → 32-bit word seçim
* PC\[1]   → 32-bit word içindeki 16-bit alt/üst seçim
* PC\[0]   → Her zaman 0 (çünkü 16-bit minimum hizalama)

---

![alt text](align_buffer.svg)


### Kısa özet

* **unalign = 1**: İstenen 32-bit komut bloğun son 16-bit parcel’ındasın; komutun diğer 16 biti **bir sonraki cache line** veya set’te bulunur.
* **index + 1** işlemi yapılır; eğer index zaten maksimumsa (`all-1`), toplama **taşar** ve index sıfıra sarar — işte bu **overflow** durumudur.

### Overflow olduğunda ne olur (mantık)

* Taşma olduğunda even (üst-parça bankı) için hesaplanan index `0` olur — yani adres wrap-around yaparak en düşük set’e gider.
* Ancak bu satırın (setin) **tag** bilgisi artık orijinal (odd) satırın tag’ı ile aynı **olamaz**: çünkü even parça aslında bir sonraki fiziksel cache-line’a (bir üst tag’a) ait.
* Bu yüzden tasarımda **even.tag = odd.tag + 1** olur — yani tag bir arttırılır (increment). Bu, even satıra yazılan verinin **bir üst (sonraki) blok**a ait olduğunu belirtir.

### Örnek (anlaşılır biçimde)

* Diyelim `index = 31` (son set), `tag = T`. `unalign = 1` → even index = `31 + 1` → wrap → `even.index = 0` ve `overflow = 1`.
* Sonuç:

  * `odd` (base) satırı: set 31, tag = `T` → **lower 16 bit** (komutun alt parçası) veya o set’e ait diğer parcel’lar burada bulunur.
  * `even` (wrapped) satırı: set 0, tag = `T + 1` → **upper 16 bit** (komutun üst parçası) veya bir sonraki bloktaki parcel’lar burada saklanır.

### Sonuç — hangi parça 0. satıra yazılır?

* **0. satıra (wrap olan set’e) üst parça (upper 16-bit parcel)** yazılır, fakat o satırın tag’i bir arttırılmış (`tag+1`) olur.
* Yani 0. set fiziksel olarak alt satırın (odd) devamı değil; **bir sonraki blok**un parçasını barındırır — bu yüzden tag da bir sonraki blokun tag’ına güncellenir.

### Neden önemli?

Bu mekanizma, blok sınırından geçen (cross-boundary) 32-bit komutları doğru şekilde birleştirmek (concatenate) ve doğru tag ile saklamak için gereklidir. Overflow’u göz ardı edersen:

* Üst parça yanlış tag ile saklanır → hit/miss yanlışlığı olur → yanlış veri okunur veya gereksiz miss’ler oluşur.

![alt text](overflow.svg)




```

//-----------------------------------------------------------------------------
//
//   Program Counter (32 bits)
//   +---------------------------------------------------+
//   |    31 ... 10    |   9 ... 2   |   1   |    0      |
//   |      Tag        |    Index    | Offset|  Offset   |
//   +---------------------------------------------------+
//                            |           |
//                 ---------------      ------
//                 |  0000 0000  |        1
//                 |             |        |           If unaligned, add 1 to Index
//                 |             |->  0000 0001
//                 |                        |
//                 |                        ---------------------------------------------------------------------
//                 |                                                                                            |
//                 |             +--------------------------------+     +--------------------------------+      |
//                 |             |        Odd Instruction         |     |         Even Instruction       |      |
//                 |             |             Bank               |     |               Bank             |      |
//                 |             +--------------------------------+     +--------------------------------+      |
// Index'=00000000 |-> Entry 0:  | Upprt 16 bits of 32-bit Inst A |    | Lower 16 bits of 32-bit Inst A   |     |
//                     Entry 1:  | Lower 16 bits of 32-bit Inst C |    | 16-bit Inst B                    | <---| <----  Index'=00000001
//                     Entry 2:  |  16-bit Inst E                 |    | Upprt 16 bits of 32-bit Inst C   |
//                     Entry 3:  | ...                            |    |                                  |
//                               +--------------------------------+    +----------------------------------+
//                                                         \                /
//                                                          \      32      /
//                                                           \    bits    /
//                                                            \----------/
//                                                               Concatenate
//                                                                 32-bit
//                                                               Instruction
//                                                                  ↓
//                                                               To Decoder
//
// In this design, each 32-bit instruction is split into two 16-bit parcels (lower/upper).
// - Odd bank stores the lower parcels (or partial instructions when Index is base).
// - Even bank stores the upper parcels (or the next part of the instruction if unaligned).
// If the requested instruction is unaligned (PC[1] == 1 and BOFFSET-based check),
// the Index for the even bank is incremented by 1 (overflow logic).
// The final 32-bit instruction is formed by concatenating the relevant parcels.
//-----------------------------------------------------------------------------
```



## Kod Bölümleri

```
  typedef struct packed {
    logic                                      valid;
    logic                                      match;
    logic                                      miss;
    logic                                      hit;
    logic [IDX_WIDTH-1:0]                      rd_idx;
    logic [IDX_WIDTH-1:0]                      data_wr_idx;
    logic                                      tag_wr_en;
    logic [NUM_PARCELS/2-1:0][PARCEL_BITS-1:0] wr_parcel;
    logic [NUM_PARCELS/2-1:0][PARCEL_BITS-1:0] rd_parcel;
    logic [TAG_SIZE:0]                         rd_tag;
    logic [TAG_SIZE:0]                         wr_tag;
    logic [PARCEL_BITS-1:0]                    parcel;
    logic [PARCEL_BITS-1:0]                    deviceX_parcel;
  } bank_t;
  bank_t even, odd;
```

Görüldüğü üzere bank başına tutulacak bilgiler;
- Tagin valid olduğunu bildiren valid sinyali
- İstek tagi ile bellekteki tagin eşleştiğini bildiren match sinyali
- hit miss sinyalleri
- okuma ve yazma indexleri
- tag ve data array yazma enable sinyalleri
- yazılacak ve okunacak parcel ve tagler


```
    half_sel                = buff_req_i.addr[1];  // word içindeki half indexi
    word_sel                = buff_req_i.addr[OFFSET_WIDTH-1:2];
```

- Bu iki sinyal çok öneli word select set içinde hangi wordü seçtiğimizi ve half select ise o wordün alt parcelini mi yani 16 bitini mi yoksa üst parcelini mi seçtiğimizi söyler
- Tabi özel durum olarak son wordün son parceli unalign access durumunu oluşturur.
- 32 bitten yüksek block size kullandığımızdan üst maddedeki istisnai durum hariç hepsine tek setten erişebiliriz.

aşağıdak isatır son wordün son parceli için bütün bitlerin bir olması gerekiyor demek
```
unalign                 = &{word_sel, half_sel};
```


Bir diğer önemli mevzu şu ki, bazen unalig durumu son sette ise bir sonraki set wrap durumu oluştuğu için 0. seti göstermeli bu istisnai durumu da belirlemeliyiz.

Aşağıdaki satır unalign durumunda rd_idx hepsi bir ise yani son satırı gösteriyorsa, even.rd_idx'i unalign ile toplamdan elde ederek sıfırlıyor. Yani overflowdan faydalanıyor

```
{overflow, even.rd_idx} = odd.rd_idx + unalign;
```



unalign durumunda iki bank ta miss ürettiği ise iki farklı erişim ile bu lockları lowx2ten getirmemiz gerekiyor. Biz bu durumda önceliği odd bloğa verdik.

Aşağıdaki kısımdada bu öncelik kontrolleri yapılmış
```
    wr_tag                  = odd.miss ? odd.wr_tag : even.wr_tag;
    wr_idx                  = odd.miss ? odd.rd_idx : even.rd_idx;

    even.tag_wr_en          = lowX_res_i.valid && !buff_req_i.uncached && !odd.miss && even.miss;
    odd.tag_wr_en           = lowX_res_i.valid && !buff_req_i.uncached && odd.miss;
    tag_wr_en               = lowX_res_i.valid && !buff_req_i.uncached && (odd.miss || (!odd.miss && even.miss));

    even.data_wr_idx        = odd.tag_wr_en ? odd.rd_idx : even.rd_idx;
    odd.data_wr_idx         = even.tag_wr_en && !odd.tag_wr_en ? even.rd_idx : odd.rd_idx;

    data_wr_en              = even.tag_wr_en || odd.tag_wr_en;
```


Devamında şu kısım için 

```
    parcel_idx = unalign ? '0 : word_sel;
    even.parcel = unalign ? even.rd_parcel[0] : even.rd_parcel[parcel_idx+half_sel]; // blok içerisinde hizasız bir word var  adresi 2 nin katı 4 dün değil fakat unalgin da değil
    odd.parcel = odd.rd_parcel[word_sel];
```

- unalign durumunda bir sonraki bloğun ilk parceli even parcel olur herzaman
- ikinci satırda unalign değilse even parcel zaten hep alt parcel diye bir yanıolgıya düşülmesin
- Eğer adres instructionın 32 bitin üst 16'sından başlıyor diyorsa orayı even'a kaydırıp okumalıyız bu yüzdan parcel_idx+half_sel kullandık


- şu kısımda ilk state adres 4 ün tam katı ve unalign değil
- 
- 


always_comb begin : EVEN_ODD_COMBINE

  // Default case — assume both banks are valid
  buff_res_o.blk = {even.parcel, odd.parcel};

  // -------------------------------------------------------------
  // Case 1: Aligned access (unalign = 0) + lower half (half_sel = 0)
  // -------------------------------------------------------------
  if (!unalign && !half_sel) begin
    if (|miss_state && lowX_res_i.valid) begin
      // Fetch from lower memory level directly if miss occurred
      buff_res_o.blk = lowX_res_i.blk[((word_sel + 1) * WORD_BITS) - 1 -: WORD_BITS];
    end
    else if (&hit_state) begin
      // Both banks hit — combine directly (normal case)
      buff_res_o.blk = {odd.parcel, even.parcel};
    end
  end

  // -------------------------------------------------------------
  // Case 2: Upper-half aligned access (unalign = 0, half_sel = 1)
  // -------------------------------------------------------------
  else if (!unalign && half_sel) begin
    if (|miss_state && lowX_res_i.valid) begin
      // Handle partial-miss situations
      case (miss_state)
        2'b01: buff_res_o.blk = {even.deviceX_parcel, odd.parcel};  // even miss
        2'b10: buff_res_o.blk = {even.parcel, odd.deviceX_parcel};  // odd miss
        2'b00: buff_res_o.blk = {even.parcel, odd.parcel};          // both hit (rare)
        default: buff_res_o.blk = '0;                               // both miss
      endcase
    end
    else if (&hit_state) begin
      buff_res_o.blk = {even.parcel, odd.parcel};
    end
  end

  // -------------------------------------------------------------
  // Case 3: Unaligned access (spanning two blocks)
  // -------------------------------------------------------------
  else if (unalign) begin
    // When crossing boundary, concatenation will be handled separately
    // by upper-level logic or next cycle response
    // Keep default: {even.parcel, odd.parcel}
  end
end
