# LEVEL-V İşlemcisi Teknik Dokümantasyonu

## 1. Giriş

### 1.1 Amaç ve Kapsam

Bu dokümanın amacı, LEVEL-V işlemci çekirdeğinin mimarisini, tasarım kararlarını ve kullanım senaryolarını teknik ve bütüncül bir şekilde sunmaktır. Doküman hem donanım tasarımcılarını hem de düşük seviye yazılım geliştiricilerini hedefler; bu nedenle hem mikro-mimari detaylara hem de programlama/modelleme perspektifine yer verilir.

Bu metin, LEVEL-V projesinin:
- Yüksek seviye mimarisini,
- Çekirdek (core) iç yapısını,
- Bellek sistemi ve bus mimarisini,
- Çevre birimleri ve SoC entegrasyonunu,
- Doğrulama ve test altyapısını,
- Performans karakteristiğini ve yol haritasını

resmi referans niteliğinde tanımlamayı amaçlar.

### 1.2 Hedef Kullanım Senaryoları

LEVEL-V, RISC-V tabanlı, açık ve esnek bir işlemci mimarisi olarak tasarlanmıştır. Hedeflenen başlıca kullanım alanları:

- **Gömülü sistemler:** Düşük–orta seviye gömülü kontrol uygulamaları, sensör düğümleri, basit RTOS’lar.
- **Araştırma ve eğitim:** Mikro-mimari denemeler, ders/tez projeleri, yeni ISA uzantıları prototipleme.
- **SoC prototipleme:** FPGA üzerinde SoC tasarımları, özel periferik setleri ile entegrasyon.

Tasarım, parametrik yapısı ve açık kaynak doğrulama altyapısı sayesinde, hem üretim öncesi hızlı keşif çalışmalarına hem de uzun vadeli ürünleştirme süreçlerine uygun olacak şekilde kurgulanmıştır.

### 1.3 Yüksek Seviye Özellikler

LEVEL-V işlemcisinin öne çıkan mimari özellikleri özetle şunlardır:

- RISC-V tabanlı çekirdek (konkret ISA desteği ilgili bölümde ayrıntılandırılacaktır),
- Parametrik tasarım (register sayısı, pipeline derinliği, bazı buffer/queue boyutları vb. derleme zamanı seçenekler),
- Modüler RTL yapısı (core, bellek arabirimi, periferikler ve wrapper katmanları ayrı hiyerarşilerde),
- Standart test setleri ve araçlarıyla (riscv-tests, riscv-dv, riscv-formal vb.) entegre doğrulama altyapısı,
- Simülasyon (Verilator / vsim) ve formel doğrulama desteği.

Bu dokümanın geri kalanı, bu özelliklerin her birini ayrı bölümlerde detaylı olarak ele alır.

---

## 2. Mimari Genel Bakış

### 2.1 Yüksek Seviye Blok Diyagramı

LEVEL-V işlemcisi, tipik bir RISC-V tabanlı gömülü çekirdek yapısını takip eder. Yüksek seviyede aşağıdaki ana bileşenlere ayrılabilir:

- **Çekirdek (Core):**
  - Program Sayacı (PC)
  - Instruction Fetch birimi
  - Decode ve Register File erişim aşaması
  - Yürütme (ALU, şiftleyiciler, karşılaştırıcılar vb.)
  - (Varsa) yük/store birimi (Load/Store Unit – LSU)
  - (Varsa) branch tahmin/çözüm mantığı

- **Bellek Sistemi:**
  - Instruction bellek arabirimi
  - Data bellek arabirimi
  - Ortak sistem bus’ına veya yerel RAM/ROM’a erişim lojikleri

- **Çevre Birimleri (Periferikler):**
  - Temel I/O (örneğin UART, timer, GPIO vb.)
  - Bus üzerinden erişilen memory-mapped register setleri

- **Sistem Wrapper Katmanı:**
  - Çekirdek + bellek + periferiklerin üst seviye entegrasyonu
  - Dış dünya ile olan fiziksel I/O portları
  - SoC/FPGA top-level bağlantıları

Bu dokümantasyonda sözel olarak tarif edilen blok diyagram, RTL hiyerarşisi ile bire bir örtüşecek şekilde tasarlanmıştır. Her üst seviye bölümde, ilgili RTL modülleri ve dosya yolları (`rtl/core/`, `rtl/periph/`, `rtl/wrapper/` vb.) referans verilecektir.

### 2.2 Ana Alt Sistemler ve Sorumlulukları

- **Çekirdek (Core):**  Instruction akışını yönetir, register dosyasını işletir, RISC-V ISA talimatlarını çözer ve yürütür. Tüm hesaplama lojikleri ve kontrol akış mekanizmaları burada konumlanır.

- **Bellek Arabirimi:**  Çekirdeğin instruction ve data isteklerini, alt taraftaki bellek hiyerarşisine veya sistem bus’ına uygun formata dönüştürür. Alignment, erişim boyutu (byte/halfword/word) ve istisna üretimi gibi konular bu katmanda ele alınır.

- **Çevre Birimleri (Peripherals):**  Zamanlayıcı, seri port, genel amaçlı giriş/çıkış pinleri gibi dış dünya ile etkileşimi sağlayan bloklardır. Her periferik, belirlenmiş bir adres aralığına memory-mapped register’lar üzerinden bağlanır.

- **Sistem Wrapper / SoC Entegrasyonu:**  Core ve periferiklerin tek bir üst modülde birleştirildiği, saat/destan (clock/reset) ve top-level I/O portlarının tanımlandığı bileşendir. Bu katman aynı zamanda hedef platforma (örneğin belirli bir FPGA kartına) özgü pin eşleştirmelerini ve isteğe bağlı debug arayüzlerini de barındırabilir.

### 2.3 Tasarım Prensipleri

LEVEL-V mimarisinin geliştirilmesinde aşağıdaki tasarım prensipleri gözetilmiştir:

- **Basitlik ve Anlaşılabilirlik:**  Öğrenilebilir ve değiştirilebilir bir RTL yapısı hedeflenmiştir. Modül isimleri, sinyal adları ve hiyerarşi yapısı, okuyan geliştiricinin mimariyi hızlı kavramasına yardımcı olacak şekilde seçilmiştir.

- **Parametriklik ve Yeniden Kullanılabilirlik:**  Mümkün olan yerlerde parametreler üzerinden yapılandırılabilir tasarım tercih edilmiştir. Örneğin, queue derinlikleri, bazı buffer boyutları veya belirli opsiyonel özellikler parametreler ile açılıp kapatılabilir.

- **Doğrulanabilirlik:**  Mimarinin formel araçlar ve geniş kapsamlı test setleri ile doğrulanabilir olması önceliktir. Bu nedenle ara sinyal isimlendirmeleri, assertion eklenebilecek noktalar ve coverage açısından kritik yollar gözetilmiştir.

- **Performans–Alan Dengelemesi:**  Tasarım, tek bir ekstrem noktaya (maksimum performans veya minimum alan) optimize edilmek yerine, gömülü sistemler için uygun bir dengeyi hedefler. Pipeline derinliği, forwarding yapıları ve olası OoO/queue mekanizmaları bu dengeye göre seçilmiştir.

---

Devamında şu bölümler ayrı dosyalarda detaylandırılacaktır:
- 3. Çekirdek Mimarisi (`core-architecture-tr.md`)
- 4. Bellek Sistemi (`memory-system-tr.md`)
- 5. Bus ve Periferikler (`bus-and-peripherals-tr.md`)
- 6. Doğrulama ve Test Altyapısı (`verification-and-testing-tr.md`)
- 7. Performans ve Optimizasyon (`performance-and-optimization-tr.md`)
- 8. SoC Entegrasyonu ve Roadmap (`soc-integration-and-roadmap-tr.md`)
- 9. Geliştirici Rehberi (`developer-guide-tr.md`)
