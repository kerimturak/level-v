# SKY130 SRAM Macro — Liberty Fix

## Kaynak
`efabless/sky130_sram_macros` reposundan (`generate_sram_macros.sh` ile) indirildi.

## Uygulanan Düzeltme: `max_transition`

Liberty dosyasında (`*_TT_1p8V_25C.lib`) OpenSRAM jeneratörünün ürettiği
**hatalı `max_transition` değerleri** düzeltildi.

### Sorun

OpenSRAM, timing tablolarının `index_1` dizisinin son elemanını (`0.04 ns = 40 ps`)
otomatik olarak `max_transition` değerine atıyor. Bu değer karakterizasyon aralığının
üst sınırı — fiziksel bir kısıtlama değil.

```
# Orijinal (HATALI)
default_max_transition   : 0.5 ;
pin (addr0)  { max_transition : 0.04; }   # 40 ps — aşırı sıkı!
pin (wmask0) { max_transition : 0.04; }
pin (addr1)  { max_transition : 0.04; }
```

SKY130 standart hücrelerinin `max_transition` değeri **1.5 ns**. SRAM input pinleri
de standart CMOS gate olduğundan 1.5 ns'i rahatlıkla destekler.

### OpenLane'deki Etkisi

OpenROAD `repair_design` çağrısında tasarımdaki **en sıkı** `max_transition`
constraint'ini kullanır. SDC'deki `set_max_transition 0.75` yerine Liberty
pin-level 0.04 ns geçerli olur → `[ERROR RSZ-0090]` ile flow Step 16'da durur:

```
[ERROR RSZ-0090] Max transition time from SDC is 0.040ns.
Best achievable transition time is 0.043ns with a load of 0.01pF
```

### Düzeltme

```
default_max_transition   : 1.5 ;   # was 0.5
pin (addr0)  { max_transition : 1.5; }   # was 0.04
pin (wmask0) { max_transition : 1.5; }   # was 0.04
pin (addr1)  { max_transition : 1.5; }   # was 0.04
```

Orijinal dosya `.bak` uzantısıyla yedeklenmiştir.

### Referanslar

- OpenSRAM Liberty jeneratör kaynağı: `index_1` dizisinin son elemanı `max_transition` olarak atanıyor
- Bu, `efabless/sky130_sram_macros` reposundaki bilinen bir sorundur
- Tapeout projelerinde standart workaround olarak uygulanır
