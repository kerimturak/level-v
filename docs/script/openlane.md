# OpenLane ASIC Akışı (SKY130)

Bu doküman CERES RV32IMC tasarımını açık kaynak araçlarla fiziksel serimden (PnR) geçirip GDS üretmek için eklenen akışı anlatır.

## Hedef

- RTL: `ceres_wrapper`
- Akış: OpenLane (Yosys + OpenROAD + Magic + Netgen)
- PDK: SKY130 (`sky130A`)

## Eklenen Komutlar

Repo kökünden:

```bash
make asic_subrepos
make asic_setup
make asic_prep
make asic_run
make asic_report
make asic_clean
```

`asic_subrepos` komutu aşağıdaki repoları `subrepo/asic-tools/` altına alır:

- `OpenLane`
- `OpenROAD`
- `OpenROAD-flow-scripts`
- `caravel_user_project`
- `caravel`

## Ortam Değişkenleri

İhtiyaç halinde:

```bash
export OPENLANE_IMAGE=efabless/openlane:2023.09.07
export PDK_ROOT=$HOME/.volare
export PDK=sky130A
export TAG=my_run_tag
export OPENLANE_MODE=auto
```

`OPENLANE_MODE` değerleri:

- `auto`: Docker varsa Docker, yoksa local OpenLane (`subrepo/asic-tools/OpenLane`) dener
- `docker`: sadece Docker
- `local`: sadece local OpenLane

## Akış Adımları

1. `asic_setup`
   - Docker erişimini kontrol eder
   - OpenLane image’ını çeker
   - `PDK_ROOT/PDK` varlığını doğrular

2. `asic_prep`
   - `rtl/` içinden OpenLane için kaynakları toplar
   - FPGA/Vivado odaklı dosyaları hariç tutar (`xilinx_gpio_wrapper.sv`, `systessis_wrapper.sv`)
   - `asic/openlane/designs/ceres_wrapper/src` altına kopyalar
   - Docker varsa `davidsiaw/sv2v` ile `ceres_wrapper_sv2v.v` üretir (Yosys package/import parser limitleri için)

3. `asic_run`
   - `flow.tcl` ile tam akışı çalıştırır
   - Sonuçları `results/asic/openlane/ceres_wrapper/runs/<tag>` altına üretir

4. `asic_report`
   - En son koşudan temel çıktıları gösterir:
     - `metrics.csv`
     - final GDS
     - final DEF
     - final gate-level netlist

## Docker (Önerilen)

Ubuntu 22.04 için:

```bash
chmod +x script/shell/install_docker_ubuntu.sh
sudo bash script/shell/install_docker_ubuntu.sh
newgrp docker
docker run --rm hello-world
```

Ardından OpenLane'i Docker modunda çalıştır:

```bash
OPENLANE_MODE=docker make asic_setup
OPENLANE_MODE=docker make asic_run
```

## Tasarım Konfigürasyonu

Ana dosyalar:

- `asic/openlane/designs/ceres_wrapper/config.tcl`
- `asic/openlane/designs/ceres_wrapper/constraint.sdc`
- `asic/openlane/designs/ceres_wrapper/pin_order.cfg`

Başlangıç saat tanımı:

- `clk_i`
- `20 ns` (`50 MHz`)

Pilot GDS için varsayılan sentez tanımları:

- `SYNTHESIS`
- `MINIMAL_SOC`

Bu sayede cache/bpredictor daha küçük konfig ile başlar; ilk hedef akışı sona kadar geçirmek olur.

## Önemli Notlar

- Tapeout hedefi için **0 DRC** ve **0 LVS mismatch** şartını hedefle.
- İlk denemelerde `asic_run` sonrası raporları inceleyip `FP_CORE_UTIL`, `PL_TARGET_DENSITY`, `CLOCK_PERIOD` parametrelerini iteratif ayarla.
- Daha güvenli tapeout için post-layout gate-level simülasyon ve SDF doğrulaması ekle.
