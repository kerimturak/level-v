# 4. Bellek Sistemi

## 4.1 Adresleme Modeli

LEVEL-V mimarisi, RISC-V tabanlı tipik bir düz adresleme (flat address space) modelini esas alır. Bu modelde:

- Tüm bellek ve memory-mapped periferikler, tek bir lineer adres uzayında konumlanır.
- Adres genişliği, çekirdeğin konfigürasyonuna (örn. 32-bit veya 64-bit) göre belirlenir.
- Program ve veri alanları, linker betikleri ve yazılım koşu zamanı (runtime) tarafından düzenlenir.

Bu sayede hem yalın gömülü sistemler hem de daha karmaşık işletim sistemi tabanlı yapılar desteklenebilir.

## 4.2 Bellek Hiyerarşisi

LEVEL-V, projeye ve hedef platforma göre farklı bellek hiyerarşileri ile kullanılabilir:

- **Basit Yapı:**
  - Instruction ve data erişimleri, tek bir ortak RAM/ROM alanına veya ayrı instruction/data belleklerine yönlendirilebilir.
  - Cache kullanılmayan konfigürasyonlarda, çekirdek her bellek erişiminde doğrudan sistem bus’ına veya yerel RAM’e gider.

- **Gelişmiş Yapı (Opsiyonel):**
  - Instruction cache (I-Cache) ve/veya data cache (D-Cache) katmanları eklenerek bellek erişim gecikmesi azaltılabilir.
  - Prefetch mekanizmaları veya basit çizgisel (sequential) fetch optimizasyonları kullanılabilir.

Bu doküman, temel kullanıma odaklanarak öncelikle cache’siz veya minimal cache’li yapı üzerinden açıklama yapar. Var olan spesifik bir cache uygulaması varsa, ilgili RTL modülleri ve parametreler ayrıca belirtilmelidir.

## 4.3 Instruction Bellek Yolu

Instruction fetch yolu, pipeline’ın IF aşamasından başlayarak instruction belleğine kadar uzanır. Genel akış:

1. Program sayacı (PC) değeri hesaplanır.
2. PC ile işaret edilen adresten instruction belleği okunur.
3. Okunan talimat, decode aşamasına iletilir.

Instruction belleği aşağıdaki şekillerde gerçekleştirilmiş olabilir:

- FPGA üzerinde yalnızca-okunur (ROM) tarzı bir blok RAM.
- Ayrı bir instruction RAM.
- Harici bir bus üzerinden erişilen kod belleği.

Tasarımda, fetch yolunun bant genişliği (örneğin her döngüde 32-bit veya daha geniş) ve hizalama kuralları açıkça tanımlanmalıdır. Aynı zamanda, `fence.i` gibi talimatların instruction belleği üzerindeki etkisi (instruction cache iptali, pipeline flush vb.) de bu bağlamda değerlendirilir.

## 4.4 Data Bellek Yolu

Yük/sakla (load/store) işlemleri için kullanılan data yolu, LSU ile bellek arasındaki arabirimi tanımlar. Temel noktalar:

- Erişim boyutu: byte, halfword, word (veya 64-bit için doubleword).
- Endian tercihi: RISC-V mimarisine uygun olarak little-endian.
- Hizalama kuralları: Performans veya basitlik adına hizasız erişimlere izin verilip verilmediği.

Hizasız erişimlere izin verilmiyorsa:

- Hizasız erişim tespitinde istisna üretilir.
- Yazılım katmanı, bu durumu trap handler üzerinden yönetir.

İzin veriliyorsa:

- RTL seviyesinde çoklu bellek erişimi ve veri birleştirme/dilimleme lojikleri kullanılır.
- Bu, hem alan hem de karmaşıklık maliyetini artırabilir.

## 4.5 Bellek Haritalaması

LEVEL-V tabanlı bir sistemde tipik bir bellek haritası şu alt alanlardan oluşabilir:

- **Kod Belleği (Flash/ROM):** Başlangıç adresinden itibaren program kodu.
- **Veri RAM’i:** Yığın (stack), global/değişken veri alanları.
- **MMIO Alanı:** Çevre birimlerine ayrılmış, memory-mapped register’ların yer aldığı aralık.

Örnek (temsili) bir 32-bit adres haritası:

- `0x0000_0000` – `0x0FFF_FFFF`: Kod ve veri RAM/ROM alanı.
- `0x1000_0000` – `0x1FFF_FFFF`: Çevre birimleri (UART, timer, GPIO vb.).

Gerçek projede kullanılan adres aralıkları, RTL’deki sabitler ve üst seviye wrapper modüllerle uyumlu olacak şekilde ayrı bir "Bellek Haritası" tablosunda dokümante edilmelidir.

## 4.6 fence.i Talimatı ve Instruction Belleği

RISC-V `fence.i` talimatı, instruction akışı ile data belleği arasındaki tutarlılığı sağlamak için kullanılır. LEVEL-V’de bu talimatın tipik rolü şunlardır:

- Kendi kendini değiştiren kod (self-modifying code) veya dinamik kod yükleme senaryolarında, data belleğine yazılan yeni talimatların, instruction fetch aşaması tarafından doğru şekilde görülmesini sağlamak.
- Instruction cache kullanılan sistemlerde, ilgili cache çizgilerinin geçersiz kılınması (invalidate) veya yenilenmesi.

LEVEL-V, `fence.i` talimatını en azından aşağıdaki şekilde ele almalıdır:

- Pipeline’daki bekleyen instruction/data erişimlerini tamamladıktan sonra, instruction fetch yolunu senkronize etmek.
- Gerekirse instruction cache veya fetch buffer yapılarında uygun flush/invalidasyon işlemlerini tetiklemek.

Bu davranış, hem donanım tasarımı hem de yazılım tarafında (derleyici, runtime, işletim sistemi) açıkça dokümante edilmelidir.

## 4.7 Hata Durumları ve İstisnalar

Bellek sistemi ile ilgili çeşitli hata durumları istisna (exception) üretilmesine yol açabilir:

- Geçersiz veya ayrılmamış adres alanına erişim.
- Sadece-okunur bölgelerde yazma denemesi.
- Hizasız erişim (eğer desteklenmiyorsa).

Bu durumlarda:

- İlgili erişim iptal edilir.
- İstisna sebebi ve hatalı erişim adresi, belirlenmiş kontrol register’larında saklanır.
- Kontrol akışı, istisna handler adresine yönlendirilir.

Bu mekanizmalar, "İstisna ve Kesme" bölümünde çekirdek perspektifinden yeniden ele alınacaktır; burada bellek sistemi ile ilişkili tarafı vurgulanmıştır.
