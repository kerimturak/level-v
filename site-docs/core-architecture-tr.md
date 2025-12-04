# 3. Çekirdek Mimarisi

## 3.1 ISA Desteği

LEVEL-V çekirdeği, RISC-V tabanlı bir işlemci olarak tasarlanmıştır. Desteklenen temel talimat seti ve uzantılar, hedef kullanım senaryolarına göre yapılandırılabilir olacak şekilde düşünülmüştür. Genel yaklaşım aşağıdaki prensipleri izler:

- **Temel ISA:** 32-bit veya 64-bit adresleme moduna uygun, RV32I / RV64I benzeri temel integer talimat seti.
- **Standart Uzantılar:** Uygun görülen durumlarda M (çarpma/bölme), C (sıkıştırılmış talimatlar) ve muhtemel diğer standart uzantıların eklenebilmesi.
- **Özel Uzantılar:** Gelecekte proje ihtiyaçlarına göre özel talimatların (örneğin hızlandırılmış kriptografi, bitmanipülasyon veya DSP-benzeri işlemler) eklenebilmesi.

Bu doküman, belirli bir konfigürasyon için derlenen LEVEL-V çekirdeğinin hangi uzantıları desteklediğini ayrıca belirtmelidir. Bu sayede derleyici (compiler) ve derleme zinciri (toolchain) düzgün yapılandırılabilir.

## 3.2 Register Dosyası ve Program Modeli

Çekirdek, RISC-V programlama modeline uygun genel amaçlı register (GPR) dosyasına sahiptir. Genel olarak aşağıdaki özellikler geçerlidir:

- Sabit sayıdaki genel amaçlı register (örneğin 32 adet x0–x31).
- `x0` register’ının her zaman sabit 0 değeri okuması.
- İmza register’larının (örneğin yığın işaretçisi `sp`, global pointer `gp`, frame pointer `fp`, dönüş adresi `ra` vb.) RISC-V ABI’ye uygun olarak konumlandırılması.

Register dosyası, tipik olarak aşağıdaki tasarım tercihleri ile uygulanır:

- **Çift okuma, tek yazma portu** (2R1W) veya pipeline gereksinimlerine uygun port sayısı.
- Okuma ve yazma saat kenarına göre senkron/asenkron tercihleri.
- Forwarding/bypass yapıları ile etkileşim (ilgili pipeline bölümünde açıklanacaktır).

Bu yapı, hem yazılım seviyesindeki fonksiyon çağırma sözleşmelerini (calling convention) hem de donanım seviyesindeki pipeline bağımlılık çözüm mekanizmalarını etkiler.

## 3.3 Pipeline Yapısı

LEVEL-V çekirdeği, gömülü odaklı ama performans–alan dengesini gözeten bir pipeline mimarisi ile tasarlanmıştır. Genel pipeline aşamaları klasik RISC yapısına benzer:

1. **IF (Instruction Fetch):** Program sayacına (PC) göre ilgili talimatın instruction belleğinden okunması.
2. **ID (Instruction Decode / Register Fetch):** Talimatın çözümlenmesi, kaynak register’ların okunması.
3. **EX (Execute):** ALU işlemlerinin, adres hesaplamalarının ve branch koşullarının değerlendirilmesi.
4. **MEM (Memory Access):** Yük (load) ve sakla (store) talimatları için veri belleğine erişim.
5. **WB (Write Back):** Hesaplanan sonucun ilgili hedef register’a yazılması.

Gerçek LEVEL-V uygulanması, hedef frekans, alan ve güç sınırlamalarına bağlı olarak bu aşamaları birleştirebilir veya daha ince aşamalara bölebilir. Örneğin:

- IF ve ID aşamalarının tek bir döngüde birleştirilmesi,
- EX aşamasının karmaşık çarpma/bölme birimleri için birden fazla döngüye yayılan bir pipeline’a sahip olması,
- MEM aşamasının bus protokolünün el sıkışma (handshake) süresine göre değişken gecikmeli olması.

Bu pipeline yapısı, veri ve kontrol bağımlılıklarının nasıl ele alındığını, hangi noktalarda baloncuk (bubble) eklendiğini ve hangi durumlarda stall üretildiğini doğrudan belirler.

## 3.4 Veri Bağımlılıkları ve Forwarding

Pipeline’lı tasarımlarda ardışık talimatlar arasında veri bağımlılıkları kaçınılmazdır. LEVEL-V bu bağımlılıkları aşağıdaki mekanizmalarla yönetir:

- **Forwarding/Bypass Yolları:**
  - EX veya MEM aşamasında üretilen sonuçların, henüz register dosyasına yazılmadan bir sonraki talimatın EX aşamasına yönlendirilmesi.
  - Böylece tipik `ADD` ardından `SUB` gibi basit bağımlı dizilerde ek bekleme döngüsü (stall) gerekmemesi.

- **Stall Mekanizması:**
  - Forwarding ile çözülemeyen durumlarda (özellikle load-use bağımlılıkları), pipeline belirli aşamalarda durdurularak güvenli yürütme sağlanır.
  - Bu durumlarda IF/ID aşamalarına baloncuk enjekte edilir ve bağımlı talimatın doğru veriyi alması beklenir.

LEVEL-V’nin RTL tasarımında, bu mekanizmalar genellikle özel kontrol birimleri (hazard detection unit vb.) ile gerçekleştirilir. Bu birimler, talimat alanları ve register numaraları üzerinden bağımlılık analizini çevrim bazında yapar.

## 3.5 Kontrol Akışı ve Dallanma İşlemleri

Kontrol akışı talimatları (branch, jump, call/return vb.) pipeline tasarımı açısından kritik önem taşır. LEVEL-V tasarımında:

- Basit bir **statik branch tahmin** stratejisi (örneğin “her zaman not-taken” veya belirli talimat tiplerine göre sabit tahmin) veya
- Daha gelişmiş bir **dinamik tahmin mekanizması** (branch history tabloları, pattern history, BTB vb.)

kullanılabilecek şekilde mimari esneklik öngörülmüştür.

Genel yaklaşım şu adımları kapsar:

- Branch talimatı ID veya EX aşamasında çözülür.
- Eğer daha önce tahmin edilen yol yanlışsa, pipeline flush edilir ve doğru hedef adresten yeniden fetch yapılır.
- Flush işlemi sırasında, yanlış yoldaki talimatlar geçersiz sayılır ve yan etkileri (register/bellek yazımları) engellenir.

Bu mekanizma, hem kontrol bağımlılıklarının doğru yönetilmesini hem de gereksiz performans kayıplarının minimize edilmesini amaçlar.

## 3.6 Yük/Sakla (Load/Store) Birimi

LEVEL-V çekirdeğinde yük/sakla işlemlerinden sorumlu özel bir Load/Store Unit (LSU) bulunur. LSU’nun temel görevleri:

- Adres hesaplamasını EX aşamasından almak ve bellek isteğini oluşturmak.
- Erişim boyutuna (byte/halfword/word) ve hizalamaya (alignment) göre veriyi doğru şekilde düzenlemek.
- Bellekten okunan veriyi gerektiğinde işaret genişletme (sign/zero extension) kurallarına göre register dosyasına aktarmak.

LSU, sistem bus’ı veya bellek arabirimi ile tipik olarak el sıkışma (valid/ready, req/ack vb.) sinyalleri üzerinden haberleşir. Bu sırada:

- Bekleme süresi olan erişimlerde (örneğin harici RAM, yavaş bus), pipeline MEM aşamasında stall edilir.
- Hatalı erişimlerde (korunmayan adres alanları, hizasız erişimler vb.) istisna (exception) üretilebilir.

## 3.7 İstisna ve Kesme (Exception/Interrupt) Desteği

LEVEL-V, RISC-V uyumlu veya projeye özgü bir istisna/interrupt modelini destekleyecek şekilde tasarlanmıştır. Genel hatlarıyla:

- **Senkron İstisnalar:**
  - Geçersiz talimat, hizasız erişim, korumasız bellek erişimi gibi olaylar.
  - Genellikle ilgili talimatın yürütüldüğü pipeline aşamasında tespit edilir.

- **Asenkron Kesintiler (Interrupt):**
  - Dış dünyadan veya çevre birimlerinden gelen zamanlayıcı, harici sinyal vb. kaynaklı uyarılar.
  - Pipeline’ın belirli, iyi tanımlanmış noktalarında çekirdek tarafından “alınır” ve servis edilir.

İstisna ve kesmeler için tipik olarak şu bileşenler bulunur:

- İstisna sebebini, program sayacını ve gerekirse ek durumu saklayan kontrol register’ları.
- Kesme maskeleme ve önceliklendirme mekanizmaları.
- İstisna/interrupt giriş ve çıkış yollarını yöneten kontrol durumu makinesi (FSM).

Bu mekanizma sayesinde çekirdek, hatalı durumlara ve dış dünyadan gelen olaylara deterministik ve kontrol edilebilir bir şekilde tepki verebilir.

## 3.8 Mikro-Mimari Esneklik ve Özelleştirme

LEVEL-V çekirdeği, farklı hedeflere yönelik olarak şu eksenlerde özelleştirilebilir olacak şekilde kurgulanmıştır:

- **Pipeline Derinliği:** Daha yüksek frekans hedefleri için pipeline aşamalarının ayrıştırılması, düşük güç/alan hedefleri için daha sığ pipeline.
- **Uzantılar:** ISA uzantılarının (M, C, özel talimatlar vb.) isteğe göre açılıp kapatılması.
- **Queue/Buffer Yapıları:** Fetch queue, load/store queue vb. yapıların derinlikleri.

Bu esneklik, RTL seviyesinde parametreler ve `generate` blokları kullanılarak sağlanır. Aynı kod tabanından, farklı konfigürasyonlar derlenebilmesi amaçlanır.
