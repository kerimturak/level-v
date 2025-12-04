# 7. Performans ve Optimizasyon

## 7.1 Performans Hedefleri

LEVEL-V işlemcisi, gömülü odaklı ancak ölçeklenebilir bir performans profili sunmayı hedefler. Temel tasarım hedefleri şunlardır:

- Orta seviye saat frekanslarında stabil çalışma (hedef FPGA/ASIC teknolojisine bağlı olarak),
- Makul IPC (instructions per cycle) değeri,
- Alan (LUT/FF, gate sayısı) ve güç tüketimi ile performans arasında dengeli bir tasarım.

Bu hedefler, uygulanacak pipeline derinliği, forwarding yapıları ve opsiyonel uzantılar (M, C vb.) ile doğrudan ilişkilidir.

## 7.2 CoreMark Performansı

CoreMark, gömülü işlemciler için yaygın olarak kullanılan bir performans benchmark’ıdır. LEVEL-V için:

- `env/coremark/` ve `docs/COREMARK_BUILD.md` altında, CoreMark’ın derlenmesi ve çalıştırılmasına yönelik talimatlar bulunabilir.
- Benchmark tipik olarak belirli bir saat frekansı ve derleyici ayarları (optimizasyon seviyeleri, kullanılan kütüphaneler) ile koşulur.

Dokümantasyonda yer verilmesi önerilen metrikler:

- **CoreMark skoru:** Toplam puan.
- **CoreMark/MHz:** Saat frekansından bağımsız karşılaştırma için normalize değer.
- Test koşullarının detayları (frekans, hedef platform, derleyici versiyonu, kullanılan derleme bayrakları).

## 7.3 Dhrystone ve Diğer Benchmark’lar

Dhrystone, tarihsel olarak yaygın kullanılan bir başka sentetik benchmark’tır. Bunun yanında Embench gibi daha modern ve uygulamaya yakın test setleri de kullanılabilir.

- `env/dhrystone/` ve `env/embench/` dizinleri, bu benchmark’ların entegrasyonuna işaret eder.
- Her benchmark için, elde edilen skorlar, koşullar ve gözlemler ayrı bir tablo halinde sunulmalıdır.

Önerilen raporlama biçimi:

- Benchmark adı (CoreMark, Dhrystone, Embench test listesi vb.).
- Toplam skor veya ilgili metrik (örneğin DMIPS/MHz).
- Test sırasında kullanılan sistem konfigürasyonu.

## 7.4 Mikro-Mimari Optimizasyonlar

LEVEL-V’nin performansını artırmak için uygulanabilecek çeşitli mikro-mimari teknikler bulunmaktadır:

- **Forwarding / Bypass:** Veri bağımlılıklarında gereksiz stall sayısını azaltır.
- **Branch Tahmini:** Kontrol akışı belirsizliğinden kaynaklanan pipeline flush sayısını düşürür.
- **Daha Derin Pipeline:** Daha yüksek saat frekansına izin verebilir, ancak branch cezasını ve stall ihtimallerini artırabilir.
- **Bellek Arabirimi Optimizasyonları:** Burst erişimler, yazma tamponları (write buffer), basit prefetch mekanizmaları.

Bu optimizasyonların her biri, alan ve tasarım karmaşıklığı üzerinde bedel doğurur; bu nedenle proje hedeflerine göre seçilmelidir.

## 7.5 Alan ve Güç Ticareti

Performans kadar, özellikle FPGA veya düşük güç hedefli ASIC tasarımlarında alan ve güç tüketimi de kritik metriklerdir. LEVEL-V’de:

- Opsiyonel uzantılar ve gelişmiş özellikler (örneğin karmaşık branch predictor veya büyük buffer’lar) kapatılarak daha küçük bir konfigürasyon elde edilebilir.
- Çoklu pipeline aşamalarının birleştirilmesiyle hem alan azalabilir hem de saat frekansı düşebilir; bazı gömülü senaryolarda bu istenen bir durumdur.

Bu ticaretler, dokümantasyonda "Hafif Konfigürasyon" ve "Yüksek Performans Konfigürasyonu" gibi örnek profillerle anlatılabilir.

## 7.6 Gelecek Optimizasyon Planları

LEVEL-V’nin gelişimi devam ettikçe, aşağıdaki alanlarda ilave optimizasyonlar planlanabilir:

- Daha gelişmiş branch tahmin mekanizmaları (iki seviyeli tahmin, BTB, RAS vb.).
- Veri ön getirme (data prefetching) ve instruction prefetching teknikleri.
- Özel talimatlar (örn. kriptografi, DSP) ile belirli iş yüklerinde hızlandırma.

Bu bölüm, proje evrildikçe güncellenmesi gereken "canlı" bir liste olarak tutulmalıdır. Böylece hem mevcut durum hem de geleceğe yönelik hedefler şeffaf bir şekilde izlenebilir.
