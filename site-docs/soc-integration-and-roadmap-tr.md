# 8. SoC Entegrasyonu ve Roadmap

## 8.1 SoC İçinde Konumlandırma

LEVEL-V çekirdeği, tipik olarak daha büyük bir System-on-Chip (SoC) tasarımı içerisinde konumlandırılır. Bu bağlamda:

- Çekirdek, sistem bus’ına bir master olarak bağlanır.
- Bellek denetleyicileri, çevre birimleri ve diğer hızlandırıcı IP blokları aynı bus üzerinde slave olarak bulunur.
- Ortak saat (clock) ve reset ağları üzerinden senkronizasyon sağlanır.

SoC top-level modülü, çekirdeğin çevresini sarmalayan ve harici pinlere (I/O’lara) kadar uzanan tüm bağlantıları içerir. Bu modül ayrıca, belirli FPGA kartları veya ASIC padframe’leri için pin eşleştirme dosyaları (constraints) ile birlikte kullanılır.

## 8.2 Bellek ve Periferik Seti

LEVEL-V tabanlı örnek bir SoC konfigürasyonu şu bileşenleri içerebilir:

- Bir veya daha fazla RAM bloğu (instruction/data için paylaşımlı veya ayrı).
- Boot kodu veya sabit veriler için ROM/Flash arabirimi.
- UART, timer, GPIO gibi temel çevre birimleri.
- Gelişmiş konfigürasyonlarda: SPI, I2C, Ethernet MAC, harici bellek denetleyicileri vb.

Bu bileşenlerin adres haritası ve bus üzerindeki konumları, "Bellek Sistemi" ve "Bus ve Periferikler" bölümleriyle tutarlı olacak şekilde dokümante edilmelidir.

## 8.3 FPGA Prototipleme

Projede, FPGA üzerinde çalıştırılabilir örnek SoC konfigürasyonları oluşturmak önemli bir adımdır. FPGA prototipleme sayesinde:

- Gerçek donanım üzerinde saat frekansı, IO davranışı ve güç tüketimi gibi metrikler gözlemlenebilir.
- Yazılım geliştiriciler, gerçek donanım üzerinde firmware ve uygulama kodu geliştirmeye başlayabilir.

Tipik FPGA akışı:

1. LEVEL-V SoC RTL top-level’inin hedef FPGA ailesine uygun olarak yapılandırılması.
2. Sentez (synthesis), yerleştirme (place) ve yönlendirme (route) adımlarının tamamlanması.
3. Üretilen bitstream’in FPGA kartına yüklenmesi.
4. Seri port üzerinden boot mesajlarının ve test çıktıların gözlemlenmesi.

Bu süreçte kullanılan kart(lar), saat frekansı, IO gerilim seviyeleri ve benzeri detaylar ayrı bir "FPGA Uygulama Notu" olarak dokümante edilebilir.

## 8.4 Yazılım Ekosistemi ve Toolchain

LEVEL-V, RISC-V ekosistemi ile uyumlu bir şekilde çalışacak şekilde tasarlandığı için:

- GCC veya LLVM tabanlı RISC-V derleyicileri,
- openOCD veya benzeri debug araçları,
- Standart C kütüphaneleri ve bare-metal/RTOS ortamları,

ile entegre edilebilir.

Yazılım tarafında tipik adımlar:

- Hedefe uygun linker script ve başlangıç kodu (startup) hazırlanması.
- Temel sürücülerin (UART, timer, GPIO vb.) yazılması.
- Boot süreci ve hata ayıklama (debug) mekanizmalarının kurgulanması.

Bu adımlar, "Geliştirici Rehberi" bölümünde daha operasyonel bir bakış açısıyla ele alınacaktır.

## 8.5 Yol Haritası (Roadmap)

LEVEL-V projesi, sadece mevcut özelliklerin stabilizasyonu ile sınırlı kalmayıp, orta ve uzun vadeli gelişim hedeflerine de sahiptir. Örnek roadmap maddeleri:

- **Kısa Vadeli Hedefler:**
  - Mevcut ISA kapsamının tam doğrulanması.
  - Temel SoC konfigürasyonlarının (çekirdek + bellek + UART + timer) kararlı hale getirilmesi.
  - Başlıca benchmark’larda hedeflenen performans seviyesine ulaşılması.

- **Orta Vadeli Hedefler:**
  - Gelişmiş branch tahmini ve bellek optimizasyonları.
  - Ek periferik setlerinin (SPI, I2C, vs.) entegrasyonu.
  - Daha kapsamlı formel doğrulama kapsamı.

- **Uzun Vadeli Hedefler:**
  - Çok çekirdekli (multi-core) konfigürasyonlar.
  - Gelişmiş güvenlik özellikleri (örneğin bellek koruma üniteleri, güvenli boot).
  - Özel amaçlı hızlandırıcılarla (kriptografi, yapay zekâ, DSP vb.) daha sıkı entegrasyon.

Bu roadmap, projenin ilerleyişine göre periyodik olarak güncellenmeli ve gerçeklenmiş hedefler ile planlanan çalışmalar net bir şekilde ayrıştırılmalıdır.
