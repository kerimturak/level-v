# Bug #001: Unaligned Instruction Fetch Across Cache Lines

## Özet

Verilator simülasyonunda, cache line sınırını geçen 32-bit instruction'lar yanlış fetch ediliyordu. ModelSim'de aynı testler doğru çalışıyordu.

## Etkilenen Test

- `rv32uc-p-rvc` (RISC-V Compressed Instructions testi)

## Semptomlar

- Verilator'da test başarısız oluyordu
- ModelSim'de aynı test geçiyordu
- `0x80001ffe` adresindeki instruction yanlış okunuyordu:
  - **Beklenen (Doğru):** `0x00158593` (`addi a1, a1, 1`)
  - **Okunan (Yanlış):** `0x00008593` (`addi a1, x1, 0`)

## Kök Neden Analizi

### Adres Yapısı

```
Adres: 0x80001ffe
├── Cache Line 1 (odd):  0x80001FF0 - 0x80001FFF (16 bytes)
│   └── Instruction'ın alt 16 bit'i: 0x8593 (offset 14-15)
│
└── Cache Line 2 (even): 0x80002000 - 0x8000200F (16 bytes)
    └── Instruction'ın üst 16 bit'i: 0x0015 (offset 0-1)
```

### Problem

`align_buffer.sv` modülünde, `unalign` durumunda (instruction iki cache line'a yayıldığında) ikinci cache line için yanlış adres gönderiliyordu.

**Hatalı Kod:**

```systemverilog
case ({unalign, odd.miss, even.miss})
  3'b101:  lowX_req_o.addr = base_addr + BLOCK_BYTES;  // Sadece bu durumda ikinci cache line
  default: lowX_req_o.addr = base_addr;                 // 3'b111 dahil hep ilk cache line
endcase
```

**Senaryo:**

1. `0x80001ffe` adresine erişim istendi
2. `unalign = 1` (cache line sınırında)
3. Her iki cache line da miss: `{odd.miss, even.miss} = 2'b11`
4. **İlk cycle:** `{unalign, odd.miss, even.miss} = 3'b111`
   - İlk cache line (`0x80001FF0`) için istek gönderildi ✓
5. **Response cycle:** `lowX_res_i.valid = 1`
   - Tag RAM henüz güncellenmedi (non-blocking assignment)
   - `odd.miss` hala `1` (güncelleme sonraki cycle'da etkili)
   - `{unalign, odd.miss, even.miss} = 3'b111` hala!
   - **İkinci istek için adres:** `base_addr = 0x80001FF0` ❌ (Aynı cache line tekrar!)
   - Olması gereken: `base_addr + BLOCK_BYTES = 0x80002000`

### Neden ModelSim'de Çalışıyordu?

ModelSim ve Verilator arasında timing ve evaluation farklılıkları var. ModelSim muhtemelen:
- Delta cycle'lar arasında farklı değerlendirme yapıyordu
- Veya memory initialization farklılıkları nedeniyle farklı bir execution path izliyordu

## Çözüm

Response geldiğinde (`lowX_res_i.valid = 1`) ve her iki cache line da miss ise (`3'b111`), adres ikinci cache line'a ayarlandı:

**Düzeltilmiş Kod:**

```systemverilog
case ({unalign, odd.miss, even.miss})
  3'b101:  lowX_req_o.addr = base_addr + BLOCK_BYTES;
  3'b111:  lowX_req_o.addr = lowX_res_i.valid ? (base_addr + BLOCK_BYTES) : base_addr;
  default: lowX_req_o.addr = base_addr;
endcase
```

**Mantık:**
- `3'b111` durumunda:
  - `lowX_res_i.valid = 0`: İlk istek, `base_addr` kullan
  - `lowX_res_i.valid = 1`: İlk response geldi, ikinci cache line için `base_addr + BLOCK_BYTES` kullan

## Etkilenen Dosyalar

- `rtl/core/stage01_fetch/align_buffer.sv`

## Değişiklik

```diff
     case ({unalign, odd.miss, even.miss})
       3'b101:  lowX_req_o.addr = base_addr + BLOCK_BYTES;
+      3'b111:  lowX_req_o.addr = lowX_res_i.valid ? (base_addr + BLOCK_BYTES) : base_addr;
       default: lowX_req_o.addr = base_addr;
     endcase
```

## Test Sonuçları

### Düzeltme Öncesi
```
✗ rv32uc-p-rvc FAILED
  Spike:    0x80001ffe → 0x00158593 (addi a1, a1, 1)
  Verilator: 0x80001ffe → 0x00008593 (addi a1, x1, 0) ← YANLIŞ
```

### Düzeltme Sonrası
```
✓ rv32uc-p-rvc PASSED
  50/51 ISA testleri geçti (fence_i hariç - ayrı bir konu)
```

## Öğrenilen Dersler

1. **Simulator Farkları:** Verilator ve ModelSim arasında timing farklılıkları olabilir. Her iki simülatörde de test etmek önemli.

2. **Non-blocking Assignment Timing:** `always_ff` bloklarında non-blocking assignment (`<=`) kullanıldığında, değer sonraki clock cycle'da etkili olur. Combinational logic'te (`always_comb`) bu gecikmeyi hesaba katmak gerekir.

3. **State Machine Geçişleri:** Cache miss handling gibi multi-cycle operasyonlarda, response geldiğinde mevcut state'in ne olduğunu dikkatlice takip etmek gerekir.

## İlgili Kavramlar

- RISC-V Compressed (RVC) Instructions
- Instruction Alignment
- Cache Line Boundary Crossing
- Verilator vs ModelSim Behavioral Differences

## Tarih

- **Tespit:** 29 Kasım 2025
- **Düzeltme:** 29 Kasım 2025
