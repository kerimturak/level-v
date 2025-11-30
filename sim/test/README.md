# Test Programs & Test Lists

Bu dizin test listelerini içerir. Her test listesi, çalıştırılacak testlerin isimlerini satır satır içerir.

## 📁 Dizin Yapısı

```
sim/test/
├── riscv_test_list.flist      # ISA testleri
├── machine_csr_test.flist     # CSR testleri
├── arch_test.flist            # riscv-arch-test
├── imperas_test_list.flist    # Imperas testleri
├── riscv_benchmark.flist      # Benchmarklar
├── exception_test.flist       # Exception testleri
├── all_tests.flist            # Tüm testler
└── coremark/                  # CoreMark kaynak kodu
```

## 🔧 Konfigürasyon

Her test listesi için konfigürasyon dosyaları `script/config/tests/` dizininde bulunur:

```bash
# Mevcut konfigürasyonları listele
make list-configs

# Konfigürasyonu görüntüle
make show-config

# Belirli bir konfigürasyonla test çalıştır
make run TEST_CONFIG=isa
make run TEST_CONFIG=bench
```

## 📖 Kullanım

```bash
# ISA testlerini çalıştır
make isa

# Arch testlerini çalıştır
make arch

# Benchmark testlerini çalıştır
make bench

# Tüm testleri çalıştır
make all_tests

# Tek bir test çalıştır
make t T=rv32ui-p-add
```

## ⚠️ Not

Test binary'leri bu dizinde değil, `build/tests/` dizininde oluşturulur ve saklanır.
