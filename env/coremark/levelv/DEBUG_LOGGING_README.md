# CoreMark debug logging

This directory includes a detailed logging setup to debug the CoreMark benchmark on your core. It emits verbose messages over UART so you can see where execution stalls.

## File layout

```
env/coremark/levelv/
├── debug_log.h                    # Debug logging header
├── core_portme.c                  # Platform code with debug hooks
├── core_portme.h                  # Platform definitions
├── ee_printf.c                    # Printf implementation
├── cvt.c                          # Printf helper routines
└── DEBUG_LOGGING_README.md        # This file
```

## Debug log API

`debug_log.h` provides:

- `debug_log(msg)` — simple string
- `debug_log_int(msg, val)` — message + integer
- `debug_log_hex(msg, val)` — message + hex value
- `debug_log_int2(msg, val1, val2)` — message + two integers
- `debug_checkpoint(num)` — checkpoint marker

## Where logs are placed

### 1. `core_portme.c`
- UART init (CHECKPOINT-1, CHECKPOINT-2)
- End of platform init

### 2. `core_main.c`
- Start of `main` (CHECKPOINT-10, CHECKPOINT-11)
- Iteration configuration
- Memory allocation (CHECKPOINT-20)
- Algorithm inits (list, matrix, state)
- Init complete (CHECKPOINT-30)
- Final iteration count (CHECKPOINT-40)
- Benchmark start (CHECKPOINT-50)
- Return from `iterate()`
- Benchmark end (CHECKPOINT-60)

### 3. `iterate()`
- Iteration start
- Progress every 10 iterations
- CRC on first iteration

### 4. `core_bench_list()`
- List benchmark start
- `finder_idx` value

### 5. `core_bench_matrix()`
- Matrix benchmark start (already in patch)

### 6. `core_bench_state()`
- State benchmark start (already in patch)

## Usage

### Enable / disable

Debug logging is **on** by default. To turn it off:

```c
// In debug_log.h
#define DEBUG_LOGGING_ENABLED 0  // change from 1 to 0
```

### Build

When CoreMark is built normally, debug logs are included:

```bash
cd /path/to/level-v/subrepo/coremark
make PORT_DIR=levelv
```

or

```bash
cd /path/to/level-v/sim/test/coremark
make compile
```

### Watching UART

Messages look like:

```
[DEBUG] iterate() started
[DEBUG] Starting iterations: 1000
[CHECKPOINT-50]
[DEBUG] Iteration progress: 0
[DEBUG] Iteration progress: 10
[DEBUG] Iteration progress: 20
...
```

## Checkpoints

| Range | Meaning |
|-------|---------|
| 1–2 | UART init |
| 10–11 | `main` start and `portable_init` |
| 20 | Memory allocation done |
| 30 | All algorithms initialized |
| 40 | Final iteration count chosen |
| 50 | Benchmark timer started |
| 60 | Benchmark timer stopped |

## Finding a hang

If CoreMark stops progressing:

1. Note the last `CHECKPOINT` number.
2. Note the last debug line.
3. Together they narrow down the stall.

Example:

```
[CHECKPOINT-30]
[DEBUG] Starting benchmark timer
[CHECKPOINT-50]
[DEBUG] iterate() started
[DEBUG] Starting iterations: 1000
[DEBUG] Iteration progress: 0
[DEBUG] core_bench_list() started
[DEBUG] finder_idx: 1
```

If nothing appears after `finder_idx: 1`, the stall is likely inside `core_bench_list()`.

## Adding your own logs

1. Add `#include "../levelv/debug_log.h"` (adjust path if your tree differs).
2. Call the helpers where needed:

```c
debug_log("My custom checkpoint");
debug_log_int("Loop counter", i);
debug_log_hex("Register value", reg_val);
```

## Performance

- Logging goes through UART and **slows** the run.
- Use for bring-up only.
- For score runs, set `DEBUG_LOGGING_ENABLED` to `0`.

## Troubleshooting

### Garbled output
- Check UART baud in `core_portme.h` (`BAUD_RATE`).
- Ensure `CPU_CLK` matches the simulated clock.

### No output at all
- Confirm UART init runs.
- Check TX wiring / log capture.
- Ensure `DEBUG_LOGGING_ENABLED` is `1`.

## Sample output

A healthy run looks similar to:

```
CoreMark on Level-V RV32IMC_Zicsr
=================================
CPU Clock: 25000000 Hz
UART Baud: 115200

[DEBUG] portable_init completed
[CHECKPOINT-10]
[CHECKPOINT-11]
[DEBUG] Iterations configured: 0
[DEBUG] Execs mask: 0x7
[DEBUG] Memory allocation and assignment complete
[CHECKPOINT-20]
[DEBUG] Initializing list
[DEBUG] List init complete
[DEBUG] Initializing matrix
[DEBUG] Matrix init complete
[DEBUG] Initializing state
[DEBUG] State init complete
[CHECKPOINT-30]
[DEBUG] Auto-determining iteration count
...
```

## What was added

- `debug_log.h` created
- Logging added in `core_portme.c` and `core_main.c`
- Logging in `iterate()` and `core_bench_list()`
- Matrix/state hooks (via existing patches)
- Checkpoint numbering
- Build smoke-tested

## Contact / contributions

This flow is meant to localize CoreMark stalls. Open an issue or send a PR with improvements.
