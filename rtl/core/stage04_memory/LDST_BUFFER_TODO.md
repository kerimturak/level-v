# LD/ST Buffer — Kısa Not

## İleride Yapılacak İyileştirmeler

- **Genel merge kapsamı:** Store merge şu an güvenli/encode edilebilir maske kombinasyonlarıyla sınırlı. Tüm olası maske birleşimlerini kapsayacak daha genel birleştirme politikası eklenebilir.
- **Daha agresif forwarding penceresi:** Store-to-load forwarding şu an konservatif (in-flight dcache transaction yokken). Güvenlik korunarak in-flight sırasında da daha geniş forwarding değerlendirmesi yapılabilir.
