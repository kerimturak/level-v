# Deprecated Shell Scripts

Bu klasördeki shell scriptler artık kullanılmıyor. 
Python tabanlı runner sistemine geçildi.

## Eski → Yeni Eşleşmeleri

| Eski Script | Yeni Python Modülü |
|-------------|-------------------|
| `run_verilator.sh` | `script/python/makefile/verilator_runner.py` |
| `parse_verilator_config.sh` | `script/python/makefile/verilator_config.py` |
| `parse_modelsim_config.sh` | `script/python/makefile/modelsim_config.py` |

## Neden Değiştirildi?

1. **Bakım kolaylığı** - Python daha okunabilir ve test edilebilir
2. **JSON validasyon** - Schema-based config validation
3. **Renkli çıktı** - Tutarlı terminal formatting
4. **Platform bağımsız** - Shell'e özgü sorunlar yok
5. **Profil desteği** - Config profilleri Python'da yönetiliyor

## Silme

Bu dosyalar güvenle silinebilir:

```bash
rm -rf script/shell/deprecated/
```

---
*Deprecated on: December 2024*
