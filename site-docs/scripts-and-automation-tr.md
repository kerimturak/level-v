# LEVEL-V Script ve Otomasyon Altyapısı

Bu doküman, LEVEL-V projesinde kullanılan script ve otomasyon altyapısının hiyerarşik yapısını ve tipik kullanım senaryolarını özetler.

## 1. Genel Bakış

Otomasyon katmanı üç ana bileşenden oluşur:

1. **Kök seviye `makefile`:** Yaygın derleme, simülasyon ve test komutlarını tek noktadan sunar.
2. **`script/` dizini:** Konfigürasyon dosyaları, makefile parçaları ve Python/shell script’lerinden oluşan bir araç kutusu.
3. **Araç spesifik dosyalar (`env/`, `docs/TOOLS.md` vb.):** Harici test/benchmark ortamları ve araçlar için özel script ve rehberler.

---

## 2. Kök Seviye `makefile`

Proje kök dizinindeki `makefile`, en sık kullanılan iş akışlarını kısayol komutlar hâlinde toplar. Tipik hedefler:

- RTL’in simülasyon için derlenmesi (Verilator veya diğer simülatörler).
- Bireysel veya toplu testlerin koşturulması.
- Benchmark’ların (CoreMark, Dhrystone, Embench) derlenip çalıştırılması.
- Temizlik (clean) ve yeniden inşa (rebuild) işlemleri.

Geliştirici perspektifinden, çoğu işlem `make <hedef>` komutu ile tetiklenebilir; detaylı davranış ise `script/` ve `env/` altındaki bileşenlere delege edilir.

---

## 3. `script/` Dizin Hiyerarşisi

`script/` dizini aşağıdaki alt dizinlerden oluşur:

- `script/README.md`: Script altyapısının genel kullanımı ve önemli komutlar hakkında kısa rehber.
- `script/config/`: Konfigürasyon dosyaları (örn. hedef platform, çekirdek konfigürasyonu, test profilleri).
- `script/makefiles/`: Farklı alt görevler için parçalı makefile’lar veya include dosyaları.
- `script/python/`: Python tabanlı yardımcı araçlar (örneğin log işleme, sonuç analizi, otomatik test jenerasyonu).
- `script/shell/`: Shell script’leri (test başlatma, derleme sarmalayıcıları, ortam hazırlama vb.).

Bu yapı, ortak fonksiyonların tekrarsız ve yeniden kullanılabilir biçimde organize edilmesine imkân verir.

### 3.1 `script/config/`

Konfigürasyon dosyaları tipik olarak aşağıdaki bilgileri içerir:

- Hedef çekirdek/SOC konfigürasyon parametreleri (örn. cache boyutları, pipeline opsiyonları).
- Test profilleri (hangi test setleri, hangi simülatörle koşulacak, hangi zaman aşımı/limitler).
- Ortam değişkenleri ve yol tanımları (RISC-V toolchain yolu, simülatör yolu vb.).

Bu sayede aynı script seti, farklı konfigürasyonlarla tekrar tekrar kullanılabilir.

### 3.2 `script/makefiles/`

Bu alt dizin, kök `makefile` tarafından include edilerek kullanılan ek makefile parçalarını barındırır. Örnek işlevler:

- Farklı simülasyon araçları için derleme kuralları.
- Farklı test setleri (riscv-tests, riscv-dv, formal vb.) için özel hedefler.
- Benchmark’lar için derleme ve çalıştırma akışları.

Bu modüler yapı, make tarafındaki karmaşıklığı yönetilebilir parçalara ayırır.

### 3.3 `script/python/`

Python script’leri, daha karmaşık veri işleme ve otomasyon senaryoları için kullanılır:

- Log dosyalarının toplanması ve özet raporların üretilmesi.
- Test sonuçlarının JSON/CSV formatına dökülerek CI/CD sistemlerine feed edilmesi.
- Gerekirse otomatik test jenerasyonu veya parametre taraması (sweep) senaryoları.

Bu kısım, özellikle ileri seviye doğrulama ve performans analizi iş akışlarını destekler.

### 3.4 `script/shell/`

Shell script’leri, komut satırından hızlı kullanılabilen hafif araçlardır:

- Tek test veya küçük bir test setini koşturan yardımcı script’ler.
- Ortam hazırlama (örneğin RISC-V toolchain yolunu ayarlama, gerekli dizinleri oluşturma).
- Derleme/simülasyon komutlarını kısaltan sarmalayıcılar.

Geliştiriciler, sık kullandıkları akışları buradaki script’ler üzerinden çağırarak zaman kazanabilir.

---

## 4. Araçlar ve Dış Bağımlılıklar

Script altyapısı, çeşitli harici araçlara dayanır. Bunların kurulumu ve kullanımı hakkında detaylar genellikle `docs/TOOLS.md` ve `docs/GETTING_STARTED.md` dosyalarında yer alır. Başlıca bağımlılıklar:

- RISC-V derleyici zinciri (GCC/LLVM).
- Simülasyon araçları (Verilator, ModelSim/Questa vb.).
- Python (ve gerekirse ek kütüphaneler).
- Make ve benzeri sistem araçları.

Otomasyon script’leri, bu araçların mevcut olduğunu varsayar ve uygun hata mesajları/log’lar üzerinden sorun tespiti yapılmasına yardımcı olur.

---

## 5. Tipik Kullanım Senaryoları

Geliştiriciler için örnek akışlar:

- **Tek bir riscv-test koşturmak:**
  - İlgili `env/` alt yapısı ile test image’ini üret.
  - Kök `makefile` veya `script/shell/` altındaki bir script ile simülasyonu başlat.
- **CoreMark/Dhrystone ölçümü yapmak:**
  - `env/coremark/` veya `env/dhrystone/` altındaki script’leri kullan.
  - Sonuçları `results/` altına kaydeden Python/shell script’leri ile özetle.
- **Regresyon testi çalıştırmak:**
  - Bir test profili seç veya oluştur (`script/config/`).
  - Profili kullanan bir make hedefi veya Python script’i üzerinden çoklu testi sırayla koştur.

---

## 6. Özet

LEVEL-V’nin script ve otomasyon katmanı, farklı araç ve test setlerini tek bir tutarlı çatı altında birleştirir:

- Kök `makefile`, yüksek seviyeli giriş noktası sağlar.
- `script/` altındaki yapı, konfigürasyon, make uzantıları ve Python/shell araçlarını düzenler.
- `env/` ve `subrepo/` ile birlikte kullanıldığında, hem geliştirme sırasında hızlı iterasyon hem de geniş kapsamlı regresyon/benchmark çalışmaları için güçlü bir temel sunar.
