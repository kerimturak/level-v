# Level RISC-V — Advanced UVM Doğrulama Ortamı

`cpu` çekirdeği (5 aşamalı RV32IMC boru hattı + L1/L2 önbellek) için
kısıtlı-rastgele (constrained-random), kendi kendini kontrol eden
(self-checking) UVM 1.2 ortamı.

## Mimari

```
                        level_v_tb_top (bind: commit_if -> cpu içi)
                        ┌──────────────────────────────────────────┐
   irq_if ──────────────►                                          │
 (timer/sw/ext)         │                 cpu (DUT)                │
                        │   fetch→decode→execute→memory→writeback  │
   iomem_if ◄───────────┤   L1 I$/D$ → L2 → memory_arbiter → iomem │
 (128b satır, val/res)  └──────────────────────────────────────────┘
        ▲                                        │
        │ yanıt (reaktif)                        │ istek
┌───────┴────────┐   req_ap    ┌─────────────────▼──┐
│   mem_driver   │◄─sequencer──┤    mem_monitor     ├──txn_ap──► scoreboard
│ (gecikme+darbe)│  (req_fifo) │ (istek+yanıt gözle)│          ► coverage
└────────────────┘             └────────────────────┘
        ▲
  mem_responder_seq ◄── mem_model (sparse 4GB, hex yükleme + backdoor)
```

- **Reaktif slave bellek agent'ı** — Çekirdeğin tek bellek kapısı (iomem)
  UVM'in klasik *slave sequence* deseniyle beslenir: monitör istekleri
  sequencer içindeki `uvm_tlm_analysis_fifo`'ya yazar; sonsuz responder
  sequence isteği çeker, paylaşılan `mem_model`'den yanıtı hesaplar,
  gecikmeyi politika enum'una göre randomize eder; driver yalnızca pin sürer.
- **Rastgele program üreteci** (`rv32_program_gen`) — RV32IMC alt kümesinde,
  trap-güvenli, **kendi kendini sonlandıran** programlar üretir ve belleğe
  backdoor yükler. Beklenmeyen her istisna, programın kendi trap handler'ı
  tarafından `(mcause<<1)|1` koduyla tohost'a yazılır → FAIL.
- **tohost sözleşmesi** — Program sonunda **uncached** `tohost` adresine
  yazılan `1` PASS, diğer tek değerler FAIL demektir (riscv-tests uyumlu).
  Scoreboard bu yazmayı iomem'de görür ve `lv_test_done` uvm_event'ini
  tetikler; virtual sequence bu olayla objection'ı bırakır.
- **Watchdog** — Commit monitörü (bind edilen `commit_if`) + bellek etkinliği
  beslemesiyle; N çevrim tam hareketsizlik = kilitlenme, `UVM_FATAL`.

## Kullanılan ileri düzey UVM teknikleri

| Teknik | Nerede |
|---|---|
| Reaktif slave agent + slave sequence | `mem_agent/`, `mem_seq_lib.svh` |
| Virtual sequencer / virtual sequence | `level_v_vsequencer.svh`, `seq_lib/` |
| Hiyerarşik config object + `uvm_config_db` | `level_v_env_cfg.svh`, `level_v_env.svh` |
| Factory type override | `level_v_backpressure_test` → responder türü değişir |
| `uvm_callback` (driver kancası) | `mem_driver_cbs`, `mem_extra_delay_cb` |
| `uvm_event_pool` ile senkronizasyon | scoreboard → vseq "lv_test_done" |
| `uvm_analysis_imp_decl` çoklu abonelik | coverage, scoreboard |
| Politika-güdümlü constraint'ler (`dist`) | `mem_rsp_item`, `rv32_instr_item` |
| Constraint katmanlama (`randomize with`, knob) | vseq'ler, `irq_storm_seq` |
| SVA'lı interface + clocking block'lar | `tb/iomem_if.sv` |
| `bind` ile beyaz-kutu gözlem | `commit_if` → `cpu` içi |
| `phase_ready_to_end`, drain time, faz timeout | scoreboard, base test |
| Fonksiyonel coverage (cross'lu covergroup'lar) | `level_v_coverage.svh` |

## Koşturma

Varsayılan simülatör **Verilator**'dır (≥5.048; sürüm `make` içinde denetlenir).
UVM kaynağı olarak Verilator'ın kendi regresyonunda test ettiği düzleştirilmiş
IEEE 1800.2-2020 v3.1 (nodpi) paketi kullanılır ve repoya dahildir
(`verilator/uvm_pkg_all_nodpi.svh`, Apache-2.0/Accellera) — ek kurulum yok.
Questa/VCS/Xcelium da desteklenir:

```bash
make -C verif/uvm run                                    # duman testi (Verilator)
make -C verif/uvm run TEST=level_v_irq_stress_test SEED=7
make -C verif/uvm run TEST=level_v_backpressure_test
make -C verif/uvm regress N=50 TEST=level_v_random_stress_test
make -C verif/uvm run SIM=questa                         # ya da SIM=vcs / SIM=xrun
```

Verilator akışının bilinen sınırları:

- **covergroup'lar yok sayılır** (`COVERIGN` uyarısı): fonksiyonel coverage
  raporu için ticari simülatör kullanın. Testlerin kendisi (rastgele program,
  scoreboard kontrolleri, watchdog, arayüz SVA'ları) tam çalışır.
- `include "uvm_macros.svh"` bu akışta `verilator/` altındaki **boş shim'e**
  çözülür; makrolar düzleştirilmiş pakette zaten tanımlıdır. Ticari akışlarda
  +incdir sırası gereği gerçek dosya bulunur.
- C++ derlemesi bellek yoğundur; `VL_JOBS` (varsayılan 2) ve `VL_OPT`
  (varsayılan `-O0`) ile süre/bellek dengelenir. Kaynaklar değişmedikçe
  yeniden derlenmez (`build/uvm_verilator/Vlevel_v_tb_top`).

### Testler

| Test | Senaryo |
|---|---|
| `level_v_random_test` | Orta boy rastgele program, SMALL gecikme |
| `level_v_random_stress_test` | 1500–2000 komut, düz-rastgele gecikme |
| `level_v_irq_stress_test` | irq_mode programı + paralel kesme fırtınası |
| `level_v_backpressure_test` | HEAVY gecikme (factory override) + callback |
| `level_v_hex_test` | `+firmware=<hex>` harici imaj (riscv-dv köprüsü) |

### riscv-dv köprüsü

Ana makefile'daki `riscv_dv_gen` akışının ürettiği `.hex` imajları doğrudan
koşulabilir; `tohost` adresini imajın `link.ld`'sinden verin:

```bash
make -C verif/uvm run TEST=level_v_hex_test \
  PLUSARGS="+firmware=build/tests/riscv-dv/hex/test_0.hex +tohost_addr=0x80003000"
```

Not: cached bölgedeki (0x8000_xxxx) bir tohost'a yazma, dcache'te dirty
kalabilir ve iomem'de gecikmeli görünür; imaj `fence`/`fence.i` ile yazmayı
dışarı itiyorsa sorun olmaz. Ürettiğimiz rastgele programlar bu tuzaktan
kaçınmak için tohost'u **uncached** bölgede (0x3000_1000) tutar.

### Sık plusarg'lar

```
+n_instrs=1000       gövde uzunluğunu sabitle (randomize sonrası ezme)
+tohost_addr=0x...   tohost adresi
+lv_trace=commit.log commit trace dosyası (offline Spike diff için)
+lv_wave=dump.vcd    dalga kaydı
+wd_limit=100000     watchdog limiti (çevrim)
+iomem_assert_off    arayüz SVA'larını kapat
+clk_period_ps=8000  saat periyodu
```

## Bilinçli sınırlar / gelecek işler

- **Komut-düzeyi referans model yok**: altın model karşılaştırması repo'daki
  mevcut Spike akışıyla offline yapılır (`+lv_trace` çıktısı üzerinden).
  ISS'i DPI ile bağlamak (ör. Spike libriscv) doğal sonraki adım.
- Üreteç `jalr`/`ecall`/`ebreak`/hizasız erişim üretmez (kontrol akışı
  sözleşmesi gereği); bu yollar riscv-tests/arch-test akışlarında kapsanıyor.
- RAL (register model) yok: DUT sınırı çekirdek olduğu için memory-mapped
  register alanı bu ortamda değil; SoC-seviyesi ortamda eklenebilir.
