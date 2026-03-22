# SKY130 SRAM macro — Liberty fix

## Source

Fetched from the `efabless/sky130_sram_macros` repository (via `fetch_sky130_sram_macros_for_openlane.sh`).

## Fix applied: `max_transition`

Incorrect **`max_transition` values** produced by the OpenSRAM generator in the Liberty file (`*_TT_1p8V_25C.lib`) were corrected.

### Problem

OpenSRAM assigns the last element of the timing table `index_1` array (`0.04 ns = 40 ps`) to `max_transition`. That value is the **upper end of the characterization range**, not a physical pin constraint.

```
# Original (WRONG)
default_max_transition   : 0.5 ;
pin (addr0)  { max_transition : 0.04; }   # 40 ps — far too tight
pin (wmask0) { max_transition : 0.04; }
pin (addr1)  { max_transition : 0.04; }
```

SKY130 standard cells use **`max_transition` of 1.5 ns**. SRAM input pins are ordinary CMOS inputs and tolerate 1.5 ns comfortably.

### Effect in OpenLane

OpenROAD `repair_design` uses the **tightest** `max_transition` constraint in the design. The pin-level 0.04 ns from Liberty overrides `set_max_transition 0.75` in SDC, producing `[ERROR RSZ-0090]` and stopping the flow around step 16:

```
[ERROR RSZ-0090] Max transition time from SDC is 0.040ns.
Best achievable transition time is 0.043ns with a load of 0.01pF
```

### Correction

```
default_max_transition   : 1.5 ;   # was 0.5
pin (addr0)  { max_transition : 1.5; }   # was 0.04
pin (wmask0) { max_transition : 1.5; }   # was 0.04
pin (addr1)  { max_transition : 1.5; }   # was 0.04
```

The original file was saved with a `.bak` suffix.

### References

- OpenSRAM Liberty generator maps the last `index_1` entry to `max_transition`.
- This is a known issue in `efabless/sky130_sram_macros`.
- Adjusting Liberty is a common tape-out workaround.
