# 6. Doğrulama ve Test Altyapısı

## 6.1 Genel Yaklaşım

LEVEL-V projesinde doğrulama, tasarım sürecinin ayrılmaz bir parçası olarak ele alınmıştır. Hedef, yalnızca fonksiyonel olarak çalışan bir çekirdek elde etmek değil, aynı zamanda farklı araçlar ve test setleriyle geniş kapsamlı bir güven seviyesi sağlamaktır.

Bu kapsamda hem klasik simülasyon tabanlı doğrulama, hem de formel yöntemler ve referans test setleri kullanılır. Ayrıca performans ölçümleri için benchmark tabanlı testler de doğrulama stratejisinin bir parçası olarak değerlendirilir.

## 6.2 Kullanılan Test Setleri

Proje yapısında, `env/` ve `subrepo/` dizinleri altında çeşitli RISC-V ekosistemi test setleri ve araçları entegre edilmiştir:

- **riscv-tests / riscv-arch-test:**
  - Temel ISA ve standart uzantılar için referans kabul edilen test takımları.
  - Her talimat sınıfı ve sınır durumu için hazırlanmış assembly tabanlı testler.

- **riscv-dv:**
  - Google tarafından geliştirilen, rastgele test üretebilen (constrained random) bir doğrulama framework’ü.
  - ISA seviyesinde rastgele programlar üretip çekirdeği geniş bir girdiye maruz bırakma imkânı sunar.

- **riscv-formal:**
  - RISC-V çekirdekleri için formel doğrulama altyapısı.
  - Talimat seviyesinde özelliklerin, formel araçlar ile matematiksel olarak ispatlanmasını hedefler.

- **torture / riscv-test / diğer setler:**
  - Çeşitli topluluk projeleri ve ek testler.
  - Farklı senaryolar, corner case’ler ve yazılım seviyesinde karmaşık diziler.

Bu test setleri, LEVEL-V çekirdeğinin RISC-V uyumunu ve kararlılığını ölçmek için kullanılır.

## 6.3 Simülasyon Ortamı

LEVEL-V, ağırlıklı olarak aşağıdaki simülasyon araçları ile doğrulanır:

- **Verilator:**
  - RTL’yi C++ modeline çevirerek hızlı cycle-accurate simülasyon imkânı sağlar.
  - `build/obj_dir/` altında üretilen simülasyon wrapper’ları ve testbench bileşenleri ile birlikte kullanılır.

- **Diğer Simülatörler (örn. vsim):**
  - Klasik HDL simülatörleri ile dalga formu (waveform) analizi ve debug.
  - `vsim.wlf` gibi dosyalar, geçmiş simülasyon oturumlarına ait olabilir.

Tipik simülasyon akışı:

1. RTL kodu ve testbench derlenir.
2. Hedef test programı (örneğin bir RISC-V assembly testi veya C tabanlı benchmark) bellek image’i olarak hazırlanır.
3. Simülasyon başlatılır; çekirdek programı çalıştırırken dalga formları, register ve bellek durumları izlenir.
4. Testin başarı kriterleri (örn. belirli bir adrese "PASS" imzası yazılması) kontrol edilir.

## 6.4 Formal Doğrulama

Formel doğrulama, tasarımın belirli özelliklerinin tüm olası girişler ve durumlar için sağlandığını matematiksel olarak ispatlamayı amaçlar. LEVEL-V özelinde:

- `riscv-formal` altyapısı kullanılarak, çekirdeğin RISC-V spesifikasyonuna uygunluğu için çeşitli formel özellikler tanımlanabilir.
- Her talimat için, giriş/çıkış ilişkilerini ve yan etkileri sınırlandıran assertion’lar yazılır.
- SMT çözücüler ve formel araçlar yardımıyla, bu özelliklerin ihlal edilmediği ispatlanmaya çalışılır.

Formel doğrulama tam kapsamlı bir ispat garantisi vermese de, özellikle köşegen durumlarda (corner case) klasik simülasyonla yakalanması zor hataları ortaya çıkarma konusunda çok etkilidir.

## 6.5 Benchmark Tabanlı Doğrulama

Performans ölçümü için kullanılan benchmark’lar (örn. CoreMark, Dhrystone, Embench) aynı zamanda dolaylı bir fonksiyonel doğrulama aracı olarak da değerlendirilebilir:

- Çekirdeğin gerçekçi program akışları ve veri kalıpları altında çalışmasını sağlar.
- Compiler, kütüphaneler ve runtime ile birlikte uçtan uca (end-to-end) bir test senaryosu sunar.

`env/coremark/`, `env/dhrystone/`, `env/embench/` gibi dizinlerde, ilgili benchmark’ların derleme ve çalıştırma altyapısı bulunur (detaylar ilgili dokümanlarda açıklanmıştır).

## 6.6 Regresyon ve Sonuçların Takibi

Projede, farklı test setleri ve senaryolar düzenli olarak çalıştırılarak regresyon testleri yapılmalıdır. Bu amaçla:

- `results/` ve `results/logs/` altında, her test koşusuna ait log dosyaları ve özet raporlar tutulabilir.
- Başarılı ve başarısız testlerin istatistikleri, zaman içindeki gelişimi gösterecek şekilde arşivlenir.

Bu yaklaşım, yeni özellikler eklendikçe veya RTL’de değişiklik yapıldıkça, önceki davranışın bozulup bozulmadığının tespit edilmesini kolaylaştırır.

## 6.7 Hata Raporlama ve Takibi

Bulunan hatalar için sistematik bir raporlama ve takip süreci önerilir:

- Her hata için benzersiz bir kimlik (ID) atanması.
- Hatanın oluştuğu test, giriş koşulları, dalga formu kesitleri ve ilgili RTL kod parçalarının dokümante edilmesi.
- Çözüm için yapılan iyileştirmelerin ve sonrasında çalıştırılan doğrulama adımlarının kaydedilmesi.

Projedeki `docs/bug_report_XXX.md` benzeri dosyalar, bu sürecin yazılı izini tutmak için kullanılabilir. Böylece geçmişte karşılaşılan problemler ve çözümleri, yeni katkıda bulunan geliştiriciler için değerli bir referans haline gelir.
