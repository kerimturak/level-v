# Vivado Synthesis Fix Helpers

Bu dizin ve `Makefile.synth-fixes` tasarımınızın Vivado synthesis log'undan çıkan sorunları tespit etme, kategorize etme ve güvenli düzeltme şablonları üretme amacıyla oluşturuldu. **Bu otomatik hedefler hiç bir zaman doğrudan RTL kaynaklarını değiştirmez** — tüm öneriler manuel inceleme ve onay sonrası uygulanmalıdır.

Hızlı kullanım:

1. `make -f Makefile.synth-fixes parse` — `synthesis.log` dosyasını (`SYNTH_LOG` değiştirilebilir) hızlı şekilde parse eder ve `synth-fixes/reports/parsed.log` kaydeder.
2. `make -f Makefile.synth-fixes summary` — kısaltılmış bir özet `synth-fixes/reports/summary.txt` oluşturur.
3. `make -f Makefile.synth-fixes list-timing-loops` — kritik timing döngülerini gösterir.
4. `make -f Makefile.synth-fixes list-ram-issues` — ram inferencing sorunlarını listeler.
5. `make -f Makefile.synth-fixes generate-todo` — manuel olarak düzeltilmesi gereken noktaları `synth-fixes/patches` içine kısmi TODO dosyaları olarak çıkarır.
6. `make -f Makefile.synth-fixes propose-patches` — timing loop ve ram-inference için insan tarafından uygulanacak yama şablonları üretir.

Önemli Notlar:
- `synthesis.log` yolu `SYNTH_LOG` değişkeni ile değiştirilebilir.
- Yama şablonları örnek, açıklama amaçlıdır — kodu doğrudan değiştirmez.
- Kritik uyarılar (timing loop) genelde tasarımın pipeline/geri beslemelerini değiştirmeyi gerektirir; `set_disable_timing` gibi otomatik çözümler uzun vadede stabil değildir.

Eğer isterseniz ben bu yamalardan birini manuel olarak repo içine uygularım (önce test/CI ile, sonra commit).