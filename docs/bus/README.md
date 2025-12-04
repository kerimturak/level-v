# Wishbone Bus Interface

Bu klasör, CERES RISC-V çekirdeğinin **Wishbone B4 bus** arayüzü ile ilgili RTL modüllerini içerir.

## Modüller

### wb_master_bridge.sv
- **İşlev**: CPU'nun internal iomem arayüzünü Wishbone B4 pipelined master interface'e dönüştürür
- **Lokasyon**: `rtl/core/bus/wb_master_bridge.sv`
- **Özellikler**:
  - Single outstanding transaction support
  - Pipelined Wishbone B4 protocol
  - Byte-granular write strobes (SEL signal)
  - Error handling and timeout

### wb_interconnect.sv
- **İşlev**: Wishbone B4 1-to-N crossbar interconnect (basit address decoder)
- **Lokasyon**: `rtl/core/bus/wb_interconnect.sv`
- **Özellikler**:
  - Parametrik slave sayısı (WB_NUM_SLAVES)
  - Address-based slave selection
  - Pipelined data path
  - Error response for unmapped addresses

## Wishbone B4 Protokolü

CERES, **Wishbone B4 pipelined** bus protokolünü kullanır:
- **Data Width**: 32-bit
- **Address Width**: 32-bit
- **Byte Select**: 4-bit (SEL)
- **Burst Support**: 4-beat (128-bit cache line için)

## Slave Cihazlar

Wishbone bus'a bağlı slave cihazlar:
- **Periph Base** (0x2000_0000): Tüm peripheral'ler (UART, GPIO, SPI, I2C, Timer, etc.)
- **CLINT** (0x3000_0000): Core-local interruptor
- **External Memory** (0x4000_0000): Dış bellek arayüzü
- **RAM** (0x8000_0000): Ana RAM

## Bellek Haritası

Detaylı bellek haritası için bkz: [Memory Map](../MEMORY_MAP.md)

## Referanslar

- [Wishbone B4 Specification](https://opencores.org/downloads/wbspec_b4.pdf)
- [CERES Wishbone Bus Documentation](../WISHBONE_BUS.md)
