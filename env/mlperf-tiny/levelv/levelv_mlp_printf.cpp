/*
 * Minimal UART printf for MLPerf Tiny harness on Level-V (no %f).
 */
#include <cstdarg>
#include <cstddef>
#include <cstdint>

#include "api/internally_implemented.h"
#include "api/submitter_implemented.h"

#define UART_CTRL   (*(volatile uint32_t *)0x20000000u)
#define UART_STATUS (*(volatile uint32_t *)0x20000004u)
#define UART_RDATA  (*(volatile uint32_t *)0x20000008u)
#define UART_WDATA  (*(volatile uint32_t *)0x2000000cu)

#define UART_CTRL_TX_EN    (1u << 0)
#define UART_CTRL_RX_EN    (1u << 1)
#define UART_STATUS_TX_FULL (1u << 0)
#define UART_STATUS_RX_EMPTY (1u << 3)

static void uart_putc_raw(char c) {
  while (UART_STATUS & UART_STATUS_TX_FULL) {
  }
  UART_WDATA = (uint32_t)(unsigned char)c;
}

static void uart_put_dec(int32_t v) {
  if (v < 0) {
    uart_putc_raw('-');
    v = -v;
  }
  char buf[12];
  int i = 0;
  if (v == 0) {
    uart_putc_raw('0');
    return;
  }
  while (v > 0 && i < (int)sizeof(buf)) {
    buf[i++] = (char)('0' + (v % 10));
    v /= 10;
  }
  while (i > 0) {
    uart_putc_raw(buf[--i]);
  }
}

static void uart_put_udec(uint32_t v) {
  char buf[11];
  int i = 0;
  if (v == 0u) {
    uart_putc_raw('0');
    return;
  }
  while (v > 0u && i < (int)sizeof(buf)) {
    buf[i++] = (char)('0' + (v % 10u));
    v /= 10u;
  }
  while (i > 0) {
    uart_putc_raw(buf[--i]);
  }
}

static void uart_put_ul_hex(uint32_t v) {
  const char *xd = "0123456789abcdef";
  for (int s = 28; s >= 0; s -= 4) {
    uart_putc_raw(xd[(v >> (unsigned)s) & 0xfu]);
  }
}

int th_vprintf(const char *fmt, va_list ap) {
  int nout = 0;
  for (const char *p = fmt; *p; ++p) {
    if (*p != '%') {
      if (*p == '\n') {
        uart_putc_raw('\r');
        ++nout;
      }
      uart_putc_raw(*p);
      ++nout;
      continue;
    }
    ++p;
    if (*p == '%') {
      uart_putc_raw('%');
      ++nout;
      continue;
    }
    if (*p == 's') {
      const char *s = va_arg(ap, const char *);
      if (!s) {
        s = "(null)";
      }
      for (; *s; ++s) {
        if (*s == '\n') {
          uart_putc_raw('\r');
          ++nout;
        }
        uart_putc_raw(*s);
        ++nout;
      }
      continue;
    }
    if (*p == 'd') {
      uart_put_dec(va_arg(ap, int));
      continue;
    }
    if (*p == 'u') {
      uart_put_udec(va_arg(ap, unsigned int));
      continue;
    }
    if (*p == 'l' && p[1] == 'u') {
      ++p;
      uart_put_udec((uint32_t)va_arg(ap, unsigned long));
      continue;
    }
    if (*p == 'l' && p[1] == 'd') {
      ++p;
      uart_put_dec((int32_t)va_arg(ap, long));
      continue;
    }
    if (*p == 'p') {
      uart_put_ul_hex((uint32_t)(uintptr_t)va_arg(ap, void *));
      continue;
    }
    uart_putc_raw('%');
    uart_putc_raw(*p);
    nout += 2;
  }
  return nout;
}

void th_printf(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  (void)th_vprintf(fmt, ap);
  va_end(ap);
}
