/* ============================================================
 * Ceres-V System Calls for Embench Benchmarks
 * ============================================================
 * Minimal syscall implementations for bare-metal execution
 */

#include <stdint.h>
#include <stddef.h>
#include <sys/types.h>

/* Memory-mapped peripherals */
#define UART_BASE       0x20000000UL
#define UART_DATA       (*(volatile uint32_t*)(UART_BASE + 0x00))
#define UART_STATUS     (*(volatile uint32_t*)(UART_BASE + 0x04))
#define UART_TX_READY   (1 << 0)

/* Heap management */
extern char _heap_start;
extern char _heap_end;
static char* _heap_ptr = 0;

/* ============================================================
 * Standard C Library Functions
 * ============================================================
 */

void* memcpy(void* dest, const void* src, size_t n) {
    unsigned char* d = (unsigned char*)dest;
    const unsigned char* s = (const unsigned char*)src;
    while (n--) {
        *d++ = *s++;
    }
    return dest;
}

void* memmove(void* dest, const void* src, size_t n) {
    unsigned char* d = (unsigned char*)dest;
    const unsigned char* s = (const unsigned char*)src;
    if (d < s) {
        while (n--) {
            *d++ = *s++;
        }
    } else {
        d += n;
        s += n;
        while (n--) {
            *--d = *--s;
        }
    }
    return dest;
}

void* memset(void* s, int c, size_t n) {
    unsigned char* p = (unsigned char*)s;
    while (n--) {
        *p++ = (unsigned char)c;
    }
    return s;
}

int memcmp(const void* s1, const void* s2, size_t n) {
    const unsigned char* p1 = (const unsigned char*)s1;
    const unsigned char* p2 = (const unsigned char*)s2;
    while (n--) {
        if (*p1 != *p2) {
            return *p1 - *p2;
        }
        p1++;
        p2++;
    }
    return 0;
}

size_t strlen(const char* s) {
    const char* p = s;
    while (*p) p++;
    return p - s;
}

char* strcpy(char* dest, const char* src) {
    char* d = dest;
    while ((*d++ = *src++));
    return dest;
}

int strcmp(const char* s1, const char* s2) {
    while (*s1 && (*s1 == *s2)) {
        s1++;
        s2++;
    }
    return *(unsigned char*)s1 - *(unsigned char*)s2;
}

char* strchr(const char* s, int c) {
    while (*s) {
        if (*s == (char)c) {
            return (char*)s;
        }
        s++;
    }
    return (c == '\0') ? (char*)s : 0;
}

/* Character type table for isalpha, isdigit, etc. */
const unsigned char _ctype_[256] = {
    /* 0x00-0x1F: control characters */
    0x20,0x20,0x20,0x20,0x20,0x20,0x20,0x20,0x20,0x28,0x28,0x28,0x28,0x28,0x20,0x20,
    0x20,0x20,0x20,0x20,0x20,0x20,0x20,0x20,0x20,0x20,0x20,0x20,0x20,0x20,0x20,0x20,
    /* 0x20-0x2F: space, punctuation */
    0x88,0x10,0x10,0x10,0x10,0x10,0x10,0x10,0x10,0x10,0x10,0x10,0x10,0x10,0x10,0x10,
    /* 0x30-0x3F: digits 0-9, punctuation */
    0x04,0x04,0x04,0x04,0x04,0x04,0x04,0x04,0x04,0x04,0x10,0x10,0x10,0x10,0x10,0x10,
    /* 0x40-0x4F: @, A-O */
    0x10,0x41,0x41,0x41,0x41,0x41,0x41,0x01,0x01,0x01,0x01,0x01,0x01,0x01,0x01,0x01,
    /* 0x50-0x5F: P-Z, punctuation */
    0x01,0x01,0x01,0x01,0x01,0x01,0x01,0x01,0x01,0x01,0x01,0x10,0x10,0x10,0x10,0x10,
    /* 0x60-0x6F: `, a-o */
    0x10,0x42,0x42,0x42,0x42,0x42,0x42,0x02,0x02,0x02,0x02,0x02,0x02,0x02,0x02,0x02,
    /* 0x70-0x7F: p-z, punctuation, DEL */
    0x02,0x02,0x02,0x02,0x02,0x02,0x02,0x02,0x02,0x02,0x02,0x10,0x10,0x10,0x10,0x20,
    /* 0x80-0xFF: extended ASCII (all zero) */
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
};

/* Simple assert implementation */
void __assert_func(const char* file, int line, const char* func, const char* expr) {
    (void)file; (void)line; (void)func; (void)expr;
    /* Just halt on assertion failure */
    while(1);
}

/* ============================================================
 * UART output
 * ============================================================
 */

static void uart_putc(char c) {
    while (!(UART_STATUS & UART_TX_READY));
    UART_DATA = c;
}

static void uart_puts(const char* s) {
    while (*s) {
        uart_putc(*s++);
    }
}

static void uart_puthex(uint32_t val) {
    const char hex[] = "0123456789abcdef";
    uart_puts("0x");
    for (int i = 7; i >= 0; i--) {
        uart_putc(hex[(val >> (i * 4)) & 0xF]);
    }
}

/* ============================================================
 * System call implementations
 * ============================================================
 */

void _exit(int status) {
    uart_puts("\r\n========================================\r\n");
    uart_puts("Benchmark Complete - Exit Code: ");
    uart_puthex((uint32_t)status);
    uart_puts("\r\n========================================\r\n");
    
    /* Signal end to simulator (write to magic address) */
    volatile uint32_t* sim_ctrl = (volatile uint32_t*)0x1FFFFFFC;
    *sim_ctrl = status;
    
    /* Infinite loop */
    while (1) {
        __asm__ volatile ("wfi");
    }
}

/* Standard exit() wrapper */
void exit(int status) {
    _exit(status);
}

int _write(int fd, const char* buf, int count) {
    (void)fd;
    for (int i = 0; i < count; i++) {
        if (buf[i] == '\n') {
            uart_putc('\r');
        }
        uart_putc(buf[i]);
    }
    return count;
}

int _read(int fd, char* buf, int count) {
    (void)fd;
    (void)buf;
    (void)count;
    return 0;  /* No input */
}

void* _sbrk(ptrdiff_t incr) {
    if (_heap_ptr == 0) {
        _heap_ptr = &_heap_start;
    }
    
    char* prev_heap = _heap_ptr;
    char* new_heap = _heap_ptr + incr;
    
    if (new_heap > &_heap_end) {
        /* Out of memory */
        return (void*)-1;
    }
    
    _heap_ptr = new_heap;
    return prev_heap;
}

int _close(int fd) {
    (void)fd;
    return -1;
}

int _fstat(int fd, void* buf) {
    (void)fd;
    (void)buf;
    return -1;
}

int _isatty(int fd) {
    return (fd == 0 || fd == 1 || fd == 2) ? 1 : 0;
}

off_t _lseek(int fd, off_t offset, int whence) {
    (void)fd;
    (void)offset;
    (void)whence;
    return -1;
}

int _kill(int pid, int sig) {
    (void)pid;
    (void)sig;
    return -1;
}

int _getpid(void) {
    return 1;
}
