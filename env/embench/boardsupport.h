/* ============================================================
 * Level-V Board Support Header for Embench-IoT
 * ============================================================
 */

#ifndef BOARDSUPPORT_H
#define BOARDSUPPORT_H

/* Warmup heat - number of benchmark iterations for cache warming */
#define WARMUP_HEAT 1

/* CPU frequency for timing (MHz); match rtl/pkg/level_param.sv CPU_CLK */
#define CPU_MHZ 25

/*
 * Set by Embench's scons for each board; required by benchmark() in each src/*.
 * When building via makefile, use a conservative default (see doc/README.md).
 */
#ifndef GLOBAL_SCALE_FACTOR
#define GLOBAL_SCALE_FACTOR 1
#endif

#endif /* BOARDSUPPORT_H */
