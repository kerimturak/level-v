# 5. Bus ve Periferikler

## 5.1 Sistem Bus Mimarisi

LEVEL-V tabanlı sistemlerde, çekirdek ile bellek ve çevre birimleri arasındaki iletişim, standart bir sistem bus protokolü üzerinden gerçekleştirilir. Bu projede, sade ve yaygın kullanımı olan Wishbone benzeri bir bus yapısı öngörülmüştür (detaylar `docs/WISHBONE_BUS.md` içerisinde daha teknik seviyede ele alınabilir).

Bus mimarisinin temel hedefleri:

- Çekirdeğin instruction ve data erişimlerini, tek tip bir arabirim üzerinden dış dünyaya taşımak.
- Birden fazla master (örn. çekirdek + DMA motoru) ve birden fazla slave (RAM, ROM, UART, timer vb.) destekleyebilmek.
- Basit, kolay anlaşılabilir ve FPGA dostu bir sinyal seti sunmak.

Tipik sinyal grupları:

- Adres sinyalleri (`adr`),
- Veri giriş/çıkış sinyalleri (`dat_i`, `dat_o`),
- Denetim sinyalleri (`cyc`, `stb`, `we`, `sel`),
- El sıkışma / yanıt sinyalleri (`ack`, isteğe bağlı hata sinyalleri vb.).

## 5.2 Master ve Slave Rolleri

LEVEL-V çekirdeği genellikle sistem bus’ında bir **master** rolü üstlenir:

- Instruction fetch ve data load/store isteklerini bus üzerinden uygun slave cihazlara yönlendirir.
- Her erişim için adres, veri ve kontrol sinyallerini sürer; slave’den gelen `ack` sinyalini bekler.

**Slave** bileşenler ise şunlar olabilir:

- Ana bellek veya bellek denetleyicisi (RAM/ROM/Flash controller),
- UART, timer, GPIO gibi çevre birimleri,
- Gelişmiş sistemlerde ek hızlandırıcılar (örn. kripto, DSP blokları).

Slave’ler, kendilerine atanmış adres aralıklarına göre gelen istekleri tanımlar ve yanıtlar.

## 5.3 Adres Dekodlama ve Bus Topolojisi

Sistem bus topolojisi genellikle aşağıdaki şekilde kurgulanır:

- Tek bir master (çekirdek) ve birden fazla slave’den oluşan basit bir paylaşımlı bus.
- Adres dekoder bloğu, master’dan gelen adres sinyaline bakarak hangi slave’in etkin olacağını belirler.

Adres dekoder, tipik olarak şu işlevleri yerine getirir:

- Adresin belirli üst bitlerine göre, hedef slave’i seçmek.
- Her slave’e özgü "chip select" veya "enable" sinyallerini üretmek.
- Geçersiz adres aralıkları için ya hiçbir slave’i seçmemek ya da hata istisnası üretmek.

Bu yapı, hem RTL seviyesinde sade hem de dokümantasyon açısından takip edilebilir bir mimari sunar.

## 5.4 Temel Periferikler

LEVEL-V SoC konfigürasyonlarında, sık kullanılan birkaç temel periferik bileşen öne çıkar. Aşağıda bunların genel rol ve arayüzleri özetlenmiştir.

### 5.4.1 UART (Seri Haberleşme)

UART, dış dünya ile seri veri haberleşmesi için kullanılır. Tipik özellikler:

- Programlanabilir baud rate.
- TX (gönderim) ve RX (alım) için FIFO veya basit buffer yapıları.
- Durum register’ları (TX boş, RX dolu, hata bayrakları vb.).
- Basit kesme (interrupt) desteği (örn. RX veri geldi, TX hazır gibi olaylar için).

### 5.4.2 Timer (Zamanlayıcı)

Zamanlayıcı, periyodik kesmeler üretmek ve yazılım tarafına zaman tabanlı hizmetler sunmak için kullanılır. Temel bileşenler:

- Artan veya azalan sayaç (counter).
- Karşılaştırma register’ı (compare) ve buna bağlı kesme üretimi.
- Çeşitli çalışma modları (tek atımlık, periyodik vb.).

### 5.4.3 GPIO (Genel Amaçlı Giriş/Çıkış)

GPIO modülü, dış dünyaya basit dijital giriş/çıkış pinleri sağlar. Özellikler:

- Her pin için giriş/çıkış yönü konfigürasyonu.
- Çıkış register’ları ve giriş durumunun okunması.
- Opsiyonel olarak, pin başına kesme üretimi (örn. seviye veya kenar tetiklemeli).

Bu periferikler, tipik olarak memory-mapped register’lar üzerinden yapılandırılır ve okunur/yazılır.

## 5.5 Memory-Mapped Register Arayüzü

Tüm periferikler için ortak bir şablon önerilir:

- Her periferik, kendine atanmış adres aralığında bir veya daha fazla 32-bit (veya 64-bit) genişliğinde register sunar.
- Bu register’lar üzerinden konfigürasyon, durum okunması ve veri aktarımı yapılır.
- Register adres haritası, bit tanımları ve reset değerleri ayrıntılı bir tabloda dokümante edilmelidir.

Örneğin bir UART için tipik register seti:

- `CTRL` (kontrol register’ı): enable bitleri, baud rate ayarları vb.
- `STATUS` (durum register’ı): TX/RX durum bayrakları, hata bayrakları.
- `TXDATA` / `RXDATA`: gönderilecek/alınan veri.

Her register için:

- Adres ofseti (base address’e göre),
- Bit alanlarının ismi ve anlamı,
- Okuma/yazma izinleri (RO/WO/RW),
- Reset değerleri,

ayrıntılı olarak belirtilmelidir.

## 5.6 Kesme (Interrupt) Entegrasyonu

Periferiklerin birçoğu, kesme (interrupt) üreterek çekirdeğe olay bildirimi yapar. Tipik tasarım:

- Her periferik, bir veya daha fazla kesme çıkış hattına sahiptir.
- Bu hatlar, ortak bir interrupt kontrolcüsünde toplanarak çekirdeğe tek bir (veya sınırlı sayıda) interrupt giriş hattı üzerinden iletilir.

Interrupt kontrolcüsü:

- Her kaynağın enable/disable durumunu tutar.
- Önceliklendirme veya basit vektörleme mekanizması sunar.
- Pending (bekleyen kesme) bayraklarını yazılımın okuyup temizleyebileceği register’lar üzerinden gösterir.

Bu yapı, "İstisna ve Kesme" bölümündeki çekirdek tarafı ile birlikte düşünüldüğünde, tamamlayıcı bir kesme altyapısı sunar.

## 5.7 Genişletilebilirlik

LEVEL-V’nin bus ve periferik mimarisi, yeni bileşenlerin kolayca eklenebilmesine izin verecek şekilde modüler tasarlanmalıdır:

- Yeni bir periferik eklendiğinde, yalnızca ilgili RTL modülü ve adres dekoder güncellemesi yapılmalıdır.
- Ortak bus sinyal seti ve register şablonu korunarak, dokümantasyon ve yazılım sürücüleri açısından tutarlılık sağlanır.

Bu sayede proje büyüdükçe, eklenen her yeni bileşenin mimariye entegrasyonu öngörülebilir ve yönetilebilir olmaya devam eder.
