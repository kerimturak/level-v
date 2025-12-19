#ifndef DEBUG_LOG_H
#define DEBUG_LOG_H

#include "core_portme.h"

/* Debug logging enable/disable */
#define DEBUG_LOGGING_ENABLED 1

#if DEBUG_LOGGING_ENABLED

/* Debug log function */
static inline void debug_log(const char *msg) {
    ee_printf("[DEBUG] %s\n", msg);
}

/* Debug log with single integer parameter */
static inline void debug_log_int(const char *msg, int val) {
    ee_printf("[DEBUG] %s: %d\n", msg, val);
}

/* Debug log with hex value */
static inline void debug_log_hex(const char *msg, unsigned int val) {
    ee_printf("[DEBUG] %s: 0x%x\n", msg, val);
}

/* Debug log with two integer parameters */
static inline void debug_log_int2(const char *msg, int val1, int val2) {
    ee_printf("[DEBUG] %s: %d, %d\n", msg, val1, val2);
}

/* Checkpoint marker - just prints a checkpoint number */
static inline void debug_checkpoint(int checkpoint_num) {
    ee_printf("[CHECKPOINT-%d]\n", checkpoint_num);
}

#else

/* Disabled versions - no-op */
#define debug_log(msg)
#define debug_log_int(msg, val)
#define debug_log_hex(msg, val)
#define debug_log_int2(msg, val1, val2)
#define debug_checkpoint(num)

#endif

#endif /* DEBUG_LOG_H */
