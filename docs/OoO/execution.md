

Süper — **aynı komutu OoO bir çekirdekte adım adım yürüttüm** ve sana bir **RAT (rename) tablosu** ile **zaman çizelgesi** (Gantt) bıraktım. Üstte iki tablo ve bir grafik görüyorsun:

* **“RAT at dispatch”** : Her talimatın rename anındaki **kaynak/dest fiziksel register** eşlemesi.
* **“Execution timeline (cycles)”** : **Dispatch → Issue → Exec → WB → Commit** döngüsü, çevrim sayılarıyla.
* Grafikte:  **bar = yürütme** ,  **o = writeback** ,  **s = commit** .

## Varsayılan mikro-mimari (bu sim için)

* **Issue/commit genişliği:** 2
* **Fonksiyonel birimler:** 1×ALU (ADD, 1 çevrim), 1×MDU (MUL, 3 çevrim)
* **Rename:** her çevrim 1 talimat (in-order), ROB sıralı commit
* **Başlangıç RAT:** R1..R64 → p1..p64 (hazır @ t=0)

## Kısa bağımlılık şeması

1. `i1: MUL R1,R2 -> R3 (p65)` → **i2** R3’e bağımlı
2. `i2: ADD R3,R4 -> R5 (p66)` → **i6** R5’e bağımlı
3. `i3: ADD R2,R6 -> R7 (p67)` → **i5** R7’ye bağımlı
4. `i4: ADD R8,R9 -> R10 (p68)` → **i5** R10’a bağımlı
5. `i5: MUL R7,R10 -> R11 (p69)` → **i6** R11’e bağımlı
6. `i6: ADD R5,R11 -> R5 (p70)` — **R5’in kaynak versiyonu p66** (i2’den), **hedef p70** (WAW, rename ile çözülür)

## Çevrim-çevrim kritik olaylar (özet)

* **t1–t4:** `i1(MUL)` MDU’da; **WB@t4, Commit@t4** → `R3 = p65` hazır.
* **t3–t4:** `i3(ADD)` ALU’da;  **WB@t4** , ancak **commit@t5** (ROB sırası beklenir).
* **t4–t5:** `i2(ADD)` (R3 hazırlandıktan hemen sonra) ALU’da; **WB@t5, Commit@t5** → `R5 = p66`.
* **t5–t6:** `i4(ADD)` ALU’da; **WB/Commit@t6** → `R10 = p68`.
* **t6–t9:** `i5(MUL)` MDU’da (R7=p67 ve R10=p68 hazırlandıktan sonra); **WB/Commit@t9** → `R11 = p69`.
* **t9–t10:** `i6(ADD)` ALU’da (R5=p66 ve R11=p69 hazır); **WB/Commit@t10** → **R5’in yeni versiyonu p70** commit olur.

## Neler dikkat çekici?

* **Gerçek OoO:** `i3` ve `i4`, **i2’yi beklemeden** ilerliyor (R3 bağımlılığı yok).
* **WAW/WAR kaçınma:** `R5` iki kez yazılıyor;  **i2→p66** ,  **i6→p70** . Eski mapping (p66) i6’nın **kaynak** olarak okunuyor, yeni mapping (p70)  **hedef** .
* **Wakeup-Select:** `i2` ancak `i1` WB yaptıktan sonra uyanıp issue edilebiliyor; `i5` de hem `i3` hem `i4` tamamlanınca başlıyor.
* **Sıralı commit:** WB önce gelse de **commit** her zaman **ROB sırası** ile (i1→i2→i3→i4→i5→i6).

İstersen aynı setup’la **farklı gecikmeler** (örn. `MUL=4`, `ADD=2`),  **farklı issue/commit genişliği** , ya da **2×ALU** gibi ünite çeşitleriyle tekrar koşturup **IPC/ortalama gecikme** kıyaslarını da çıkarabilirim.
