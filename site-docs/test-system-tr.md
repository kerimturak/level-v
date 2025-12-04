# LEVEL-V Test ve Doğrulama Sistemi Hiyerarşisi

Bu doküman, LEVEL-V projesindeki test ve doğrulama altyapısının hiyerarşik yapısını ve akışını özetler. Amaç, çekirdeğin nasıl test edildiğini ve hangi klasörün hangi rolü üstlendiğini sistematik olarak açıklamaktır.

## 1. Üst Seviye Test Ekosistemi

Test ekosistemi üç ana katmandan oluşur:

1. **Test İçerikleri ve Ortamları (`env/`, `subrepo/`):**
   - RISC-V resmi/yarı-resmi test setleri, benchmark’lar ve doğrulama framework’leri.
2. **Simülasyon ve Testbench Altyapısı (`sim/`, `build/`, `rtl/tracer/` vb.):**
   - RTL çekirdeği sarmalayan testbench, hafıza model(ler)i, IO modelleri.
3. **Çalıştırma/Regresyon Script’leri (`script/`, `makefile`):**
   - Testleri derlemek, koşturmak ve sonuçları toplamak için otomasyon.

---

## 2. Env Dizin Yapısı (`env/`)

`env/` dizini, farklı test ve benchmark senaryoları için özel alt ortamlar içerir:

- `env/common/`: Ortak script’ler, konfigürasyon dosyaları veya paylaşılan kaynaklar.
- `env/coremark/`: CoreMark benchmark’ının derlenmesi ve çalıştırılması için gerekli dosyalar.
- `env/dhrystone/`: Dhrystone benchmark ortamı.
- `env/embench/`: Embench-IoT gibi modern gömülü benchmark’lar için yapılandırmalar.
- `env/imperas/`: Imperas RISC-V test ortamı ile entegrasyon.
- `env/riscv-arch-test/`: RISC-V Architecture Test Framework’ü için ortam.
- `env/riscv-dv/`: riscv-dv rastgele test üreteci entegrasyonu.
- `env/riscv-formal/`: riscv-formal tabanlı formel test ortamı.
- `env/riscv-test/`: Çeşitli RISC-V test setleri için ortam.
- `env/torture/`: riscv-torture ve benzeri stres testleri için yapılandırmalar.

Her alt dizin tipik olarak şu bileşenleri içerir:

- Test derleme script’leri (Makefile, shell/python script’leri).
- Test image’lerinin (bellek dump’ları, ELF/HEX/VMEM dosyaları) üretim adımları.
- Gerekli ise referans modellerle (ör. Spike) karşılaştırma akışları.

---

## 3. RISC-V Test Setleri ve Benchmark’lar (`subrepo/`)

`subrepo/` dizini, projeye git submodule veya dış bağımlılık olarak dahil edilen test depolarını barındırır:

- `subrepo/coremark/`: CoreMark resmi/yarı-resmi kaynakları.
- `subrepo/embench-iot/`: Embench-IoT testleri.
- `subrepo/imperas-riscv-tests/`: Imperas tarafından sağlanan RISC-V test setleri.
- `subrepo/riscv-arch-test/`: Resmi RISC-V mimari testleri.
- `subrepo/riscv-dv/`: riscv-dv doğrulama framework kodları.
- `subrepo/riscv-formal/`: riscv-formal formel doğrulama alt yapısı.
- `subrepo/riscv-tests/`: Klasik riscv-tests seti.

Bu depoların her biri, `env/` altındaki karşılık gelen ortamlarla birlikte kullanılır. Örneğin:

- `env/riscv-arch-test/` → `subrepo/riscv-arch-test/`
- `env/riscv-dv/` → `subrepo/riscv-dv/`

Böylece hem upstream testler korunur, hem de LEVEL-V’ye özgü entegrasyon script’leri proje içinde yönetilebilir.

---

## 4. Simülasyon Altyapısı (`sim/` ve `build/`)

### 4.1 `sim/` Dizin Yapısı

`sim/` dizini, simülasyon senaryolarını ve testbench yapılandırmalarını barındırır:

- `sim/README.md`: Simülasyonun genel kullanımı ve senaryolar hakkında bilgi.
- `sim/do/`: Bazı simülatörler (örn. ModelSim) için `.do` script’leri.
- `sim/tb/`: Testbench kaynak dosyaları (top-level TB modülü, hafıza modelleri, IO modelleri, clock/reset jeneratörü vb.).
- `sim/test/`: Test senaryoları, stimulus dosyaları veya wrapper’lar.

### 4.2 `build/` Dizin Yapısı

`build/` dizini, simülasyon ve diğer derleme çıktıları için çalışma alanı olarak kullanılır:

- `build/obj_dir/`: Verilator tarafından üretilen C++ simülasyon modeli (`Vceres_wrapper` vb.) ve ilgili derleme nesneleri.
- `build/logs/`: Simülasyon, test ve regresyon koşularına ait log dosyaları.
- `build/formal/`: Formel doğrulama araçları için geçici dosyalar ve log’lar.
- `build/temp/`: Geçici dosyalar, örneğin riscv-tests dönüşümleri vb.
- `build/test_work/`: Bireysel test çalışmaları için çalışma dizini (örn. `C-cadd-01_spike.cmd` gibi referans komut dosyaları).

Bu yapı sayesinde kaynak kod (`rtl/`) ve üretilmiş çıktılar (`build/`) net biçimde ayrılır.

---

## 5. Wrapper ve SoC Testi (`rtl/wrapper/`)

Testler yalnızca çekirdek seviyesinde değil, SoC seviyesinde de yürütülür. `rtl/wrapper/` dizini bu amaçla kullanılır:

- `ceres_wrapper.sv`: Çekirdeği bellek arabirimi ve basit çevre birimleri ile birlikte sarmalayan top-level modül.
- `ceres_soc.sv`: Daha geniş SoC konfigürasyonunu ifade eden üst seviye modül (çekirdek + RAM + UART + CLINT/PLIC benzeri bileşenler).
- `wb_*_slave.sv`: Wishbone tabanlı RAM/CLINT/bus slave modülleri.
- `wrapper_ram.sv`, `ram_programmer.sv`: Simülasyon ve FPGA prototipleri için RAM model ve programlayıcıları.

Simülasyon testbench’leri çoğunlukla bu wrapper modüllerini instantiate ederek, çekirdeğin gerçekçi bir SoC ortamında çalışmasını doğrular.

---

## 6. Test Çalıştırma Akışı

Yüksek seviyede tipik bir test akışı şu adımları izler:

1. **Test Programının Üretilmesi:**
   - İlgili `env/` alt dizinindeki script veya Makefile kullanılarak RISC-V programı derlenir.
   - Ortaya çıkan ELF/HEX/VMEM image’i, simülasyon belleği için uygun formata dönüştürülür.

2. **Simülasyonun Hazırlanması:**
   - Verilator veya diğer HDL simülatörleriyle `rtl/` + `rtl/wrapper/` + `sim/tb/` dosyaları derlenir.
   - `build/obj_dir/` altında simülasyon yürütücüsü (`Vceres_wrapper` vb.) üretilir.

3. **Testin Çalıştırılması:**
   - Test image’i bellek modeline yüklenir (`ram_programmer` veya simülatör komutları ile).
   - Simülasyon başlatılır; çekirdek programı çalıştırır.

4. **Sonuçların Değerlendirilmesi:**
   - Testin beklenen imza (signature) alanına yazdığı değer veya belirlenen PASS/FAIL kriterleri kontrol edilir.
   - Dalga formları (`vsim.wlf` vb.) ve loglar incelenir.

5. **Regresyon:**
   - Birden çok test aynı akışta koşturularak `results/` ve `build/logs/` altında toplanır.

Bu adımlar, proje kök dizinindeki `makefile` ve `script/` altındaki otomasyon araçlarıyla büyük oranda script’lenmiştir.

---

## 7. Sonuçların Arşivlenmesi (`results/`)

`results/` dizini, test ve regresyon koşularının kalıcı çıktılarını tutmak için kullanılır:

- `results/logs/`: Bireysel test veya regresyon log’ları.
- `results/regression/`: Toplu regresyon sonuçları, özet raporlar.

Bu dizin, özellikle CI/CD entegrasyonlarında ve uzun vadeli performans/kararlılık takibinde önemlidir.

---

## 8. Özet

LEVEL-V’nin test sistemi, hem resmi RISC-V test setlerini hem de benchmark ve formel doğrulama araçlarını bir arada kullanacak şekilde tasarlanmıştır:

- `env/` ve `subrepo/` test içeriğinin ve ortamlarının mantıklı bir ayrımını sağlar.
- `sim/` ve `build/` simülasyon ve geçici çıktıları organize eder.
- `rtl/wrapper/` SoC seviyesinde gerçekçi testler için üst seviye modüller sunar.

Bu hiyerarşi, çekirdeğin fonksiyonel doğruluğunu, performansını ve uyumluluğunu sistematik ve yeniden üretilebilir şekilde test etmeye olanak tanır.
