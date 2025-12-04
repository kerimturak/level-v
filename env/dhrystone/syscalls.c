/* ============================================================
 * Ceres-V System Calls for Dhrystone
 * ============================================================
 */

#include <stdint.h>
#include <stdarg.h>

/* Memory-mapped peripherals */
#define UART_BASE       0x20000000UL
#define UART_DATA       (*(volatile uint32_t*)(UART_BASE + 0x00))
#define UART_STATUS     (*(volatile uint32_t*)(UART_BASE + 0x04))
#define UART_TX_READY   (1 << 0)

#define CLINT_BASE      0x30000000UL
#define MTIME           (*(volatile uint64_t*)(CLINT_BASE + 0xBFF8))

/* Heap */
extern char _heap_start;
extern char _heap_end;
static char* _heap_ptr = 0;

/* Timing */
volatile uint64_t _start_time = 0;
volatile uint64_t _end_time = 0;

/* ============================================================
 * Timing Functions
 * ============================================================
 */

void start_trigger(void) {
    _start_time = MTIME;
}

void stop_trigger(void) {
    _end_time = MTIME;
}

unsigned long read_cycles(void) {
    uint32_t lo;
    __asm__ volatile ("rdcycle %0" : "=r"(lo));
    return lo;
}

/* ============================================================
 * UART Output
 * ============================================================
 */

static void uart_putc(char c) {
    while (!(UART_STATUS & UART_TX_READY));
    UART_DATA = c;
}

static void uart_puts(const char* s) {
    while (*s) {
        if (*s == '\n') uart_putc('\r');
        uart_putc(*s++);
    }
}

static void uart_putd(int val) {
    char buf[12];
    int i = 0;
    int neg = 0;
    
    if (val < 0) {
        neg = 1;
        val = -val;
    }
    
    if (val == 0) {
        buf[i++] = '0';
    } else {
        while (val > 0) {
            buf[i++] = '0' + (val % 10);
            val /= 10;
        }
    }
    
    if (neg) uart_putc('-');
    while (i > 0) uart_putc(buf[--i]);
}

static void uart_putlu(unsigned long val) {
    char buf[20];
    int i = 0;
    
    if (val == 0) {
        buf[i++] = '0';
    } else {
        while (val > 0) {
            buf[i++] = '0' + (val % 10);
            val /= 10;
        }
    }
    
    while (i > 0) uart_putc(buf[--i]);
}

static void uart_puthex(uint32_t val) {
    const char hex[] = "0123456789abcdef";
    uart_putc('0');
    uart_putc('x');
    for (int i = 7; i >= 0; i--) {
        uart_putc(hex[(val >> (i * 4)) & 0xF]);
    }
}

/* ============================================================
 * Printf Implementation (minimal)
 * ============================================================
 */

int printf(const char *format, ...) {
    va_list args;
    va_start(args, format);
    
    int count = 0;
    const char *p = format;
    
    while (*p) {
        if (*p == '%') {
            p++;
            switch (*p) {
                case 'd':
                case 'i':
                    uart_putd(va_arg(args, int));
                    break;
                case 'u':
                    uart_putlu((unsigned long)va_arg(args, unsigned int));
                    break;
                case 'l':
                    p++;
                    if (*p == 'u') {
                        uart_putlu(va_arg(args, unsigned long));
                    } else if (*p == 'd') {
                        uart_putd((int)va_arg(args, long));
                    }
                    break;
                case 'x':
                case 'X':
                    uart_puthex(va_arg(args, unsigned int));
                    break;
                case 'p':
                    uart_puthex((uint32_t)va_arg(args, void*));
                    break;
                case 's':
                    uart_puts(va_arg(args, char*));
                    break;
                case 'c':
                    uart_putc((char)va_arg(args, int));
                    break;
                case '%':
                    uart_putc('%');
                    break;
                default:
                    uart_putc('%');
                    uart_putc(*p);
                    break;
            }
        } else {
            if (*p == '\n') uart_putc('\r');
            uart_putc(*p);
        }
        p++;
        count++;
    }
    
    va_end(args);
    return count;
}

/* puts and putchar */
int puts(const char* s) {
    uart_puts(s);
    uart_putc('\r');
    uart_putc('\n');
    return 0;
}

int putchar(int c) {
    if (c == '\n') uart_putc('\r');
    uart_putc((char)c);
    return c;
}

/* ============================================================
 * String Functions
 * ============================================================
 */

char *strcpy(char *dest, const char *src) {
    char *d = dest;
    while ((*d++ = *src++));
    return dest;
}

int strcmp(const char *s1, const char *s2) {
    while (*s1 && (*s1 == *s2)) {
        s1++;
        s2++;
    }
    return *(unsigned char*)s1 - *(unsigned char*)s2;
}

/* ============================================================
 * System Calls
 * ============================================================
 */

void _exit(int status) {
    printf("\n========================================\n");
    printf("Dhrystone Complete - Exit Code: %d\n", status);
    printf("========================================\n");
    
    /* Signal to simulator */
    volatile uint32_t* sim_ctrl = (volatile uint32_t*)0x1FFFFFFC;
    *sim_ctrl = status;
    
    while (1) {
        __asm__ volatile ("wfi");
    }
}

void* _sbrk(int incr) {
    if (_heap_ptr == 0) {
        _heap_ptr = &_heap_start;
    }
    
    char* prev = _heap_ptr;
    if (_heap_ptr + incr > &_heap_end) {
        return (void*)-1;
    }
    
    _heap_ptr += incr;
    return prev;
}
