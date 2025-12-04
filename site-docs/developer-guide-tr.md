# 9. Geliştirici Rehberi

## 9.1 Depo Yapısı ve Ana Dizinler

LEVEL-V projesi, donanım tasarımı, test altyapısı ve dokümantasyonu bir arada barındıran kapsamlı bir depo yapısına sahiptir. Öne çıkan dizinler:

- `rtl/`: Çekirdek, bellek arabirimi, periferikler ve wrapper katmanları için RTL (Verilog/SystemVerilog vb.) kaynak dosyaları.
- `env/`: Çeşitli test ve benchmark ortamları (riscv-tests, riscv-dv, coremark, dhrystone, embench vb.).
- `build/`: Simülasyon ve diğer derleme çıktılarının tutulduğu dizin (obj_dir, logs vb.).
- `docs/`: Mimari, kullanım ve araçlara ilişkin ek dokümanlar.
- `script/`: Build, test ve diğer otomasyon görevleri için kullanılan script’ler.
- `sim/`: Simülasyon senaryoları, testbench dosyaları ve ilgili konfigürasyonlar.

Bu rehber, yeni bir geliştiricinin projeye hızlıca adapte olabilmesi için temel yol haritasını sunar.

## 9.2 Gereksinimler ve Kurulum

Projeyle çalışmaya başlamadan önce aşağıdaki araç ve bileşenlerin sisteminizde kurulu olması önerilir:

- Uygun bir HDL simülatörü (Verilator, vsim vb.).
- RISC-V derleyici zinciri (GCC veya LLVM tabanlı toolchain).
- Make ve benzeri komut satırı araçları.
- İlgili Python/shell script’lerini çalıştırmak için gereken yorumlayıcılar.

Detaylı kurulum adımları, `docs/GETTING_STARTED.md` ve `docs/TOOLS.md` dosyalarında daha ayrıntılı olarak bulunabilir.

## 9.3 Derleme ve Simülasyon Akışı

LEVEL-V için tipik bir çalışma döngüsü şu adımlardan oluşur:

1. **Konfigürasyon:**
   - Hedef çekirdek konfigürasyonunun ve test senaryosunun seçilmesi.

2. **Derleme:**
   - RTL ve testbench dosyalarının seçilen simülatör için derlenmesi.

3. **Simülasyon:**
   - Hedef program veya test setinin yüklenmesi.
   - Simülasyonun çalıştırılması ve sonuçların gözlenmesi.

4. **Analiz:**
   - Dalga formları, log dosyaları ve test çıktılarına bakılarak davranışın değerlendirilmesi.

Projede yer alan `makefile` ve `script/` altındaki yardımcı script’ler, bu adımların otomasyonunu kolaylaştırmak amacıyla tasarlanmıştır.

## 9.4 Test ve Regresyon Çalıştırma

Geniş kapsamlı testler ve regresyon çalışmaları için:

- `env/` altındaki test setleri ve ilgili konfigürasyon dosyaları kullanılır.
- `results/` dizinine, her koşu için log ve özet dosyalar bırakılabilir.

Önerilen yaklaşım:

- Geliştirme sırasında, öncelikle küçük ve hızlı çalışan smoke test’leri çalıştırmak.
- Büyük değişikliklerden sonra, daha kapsamlı regresyon setlerini gece veya arka planda çalıştırmak.

Bu sayede hem hızlı iterasyon sağlanır hem de uzun vadede kararlılık korunur.

## 9.5 Yeni Özellik veya Periferik Eklemek

LEVEL-V mimarisi, yeni bileşenlerin eklenmesini kolaylaştıracak şekilde modülerdir. Yeni bir özellik veya periferik eklerken tipik adımlar:

1. İlgili RTL modülünün `rtl/` altında uygun bir alt dizinde oluşturulması.
2. Sistem bus’ına bağlanması ve adres dekoderin güncellenmesi.
3. Gerekli memory-mapped register tanımlarının dokümante edilmesi.
4. Basit bir testbench veya mevcut test ortamına ek senaryolarla fonksiyonel doğrulama yapılması.
5. Gerekirse formel doğrulama veya ek benchmark’larla entegrasyonun test edilmesi.

Bu süreç, "Bus ve Periferikler" ile "Doğrulama ve Test" bölümlerinde anlatılan mimari prensiplerle uyumlu olmalıdır.

## 9.6 Katkı Rehberi

Projeye katkıda bulunmak isteyen geliştiriciler için önerilen süreç:

- Yapılacak değişikliği veya yeni özelliği kısaca dokümante etmek (amaç, kapsam, tasarım notları).
- RTL ve test değişikliklerini küçük, anlaşılır commit’lere bölmek.
- Her değişiklik için ilgili testleri güncellemek veya yeni testler eklemek.
- Hata veya beklenmedik davranış durumunda, detaylı bir bug raporu hazırlamak (giriş koşulları, dalga formu kesitleri, log dosyaları vb.).

Bu yaklaşım, projenin uzun vadede sürdürülebilir ve yönetilebilir kalmasına yardımcı olur.

## 9.7 Dokümantasyonun Güncel Tutulması

LEVEL-V gibi aktif geliştirme altındaki projelerde, dokümantasyonun kod ile uyumlu kalması kritik öneme sahiptir. Bu nedenle:

- Her önemli mimari değişiklik veya yeni özellik için ilgili dokümantasyon bölümü gözden geçirilmelidir.
- Eskiyen veya geçerliliğini yitiren içerikler zamanında güncellenmelidir.
- Otomasyon imkânı olan yerlerde (örneğin register haritaları veya parametre listeleri) dokümantasyonun kısmen araçlar tarafından üretilmesi değerlendirilebilir.

Böylece hem donanım tasarımcıları hem de yazılım geliştiriciler, LEVEL-V’nin güncel durumuna dair güvenilir bir referansa sahip olur.
