/*
 * Level-V bare-metal port of MLPerf Tiny submitter API (stub inference).
 * Official API headers live under subrepo/mlperf-tiny/benchmark/api/.
 */
#include "api/internally_implemented.h"
#include "api/submitter_implemented.h"

#include <cstdint>
#include <cstdlib>
#include <cstring>

#include "cpu_clock.h"

#define UART_CTRL   (*(volatile uint32_t *)0x20000000u)
#define UART_STATUS (*(volatile uint32_t *)0x20000004u)
#define UART_RDATA  (*(volatile uint32_t *)0x20000008u)
#define UART_WDATA  (*(volatile uint32_t *)0x2000000cu)

#define UART_CTRL_TX_EN      (1u << 0)
#define UART_CTRL_RX_EN      (1u << 1)
#define UART_STATUS_TX_FULL  (1u << 0)
#define UART_STATUS_RX_EMPTY (1u << 3)

#define TIMER_LOW (*(volatile uint32_t *)0x3000BFF8u)

static volatile uint32_t g_infer_count;

void th_load_tensor() {}

void th_infer() { ++g_infer_count; }

void th_results() {
  th_printf("m-results-[");
  for (size_t i = 0; i < 10u; i++) {
    th_printf("0.000");
    if (i + 1u < 10u) {
      th_printf(",");
    }
  }
  th_printf("]\r\n");
}

void th_pre() {}
void th_post() {}

void th_final_initialize(void) {}

void th_command_ready(char volatile *p_command) {
  ee_serial_command_parser_callback((char *)p_command);
}

int th_strncmp(const char *a, const char *b, size_t n) { return strncmp(a, b, n); }

char *th_strncpy(char *dest, const char *src, size_t n) { return strncpy(dest, src, n); }

size_t th_strnlen(const char *str, size_t maxlen) {
  size_t i = 0;
  while (i < maxlen && str[i] != '\0') {
    ++i;
  }
  return i;
}

char *th_strcat(char *dest, const char *src) { return strcat(dest, src); }

char *th_strtok(char *str1, const char *sep) { return strtok(str1, sep); }

int th_atoi(const char *str) { return atoi(str); }

void *th_memset(void *b, int c, size_t len) { return memset(b, c, len); }

void *th_memcpy(void *dst, const void *src, size_t n) { return memcpy(dst, src, n); }

void th_serialport_initialize(void) {
  uint32_t baud_div = (uint32_t)(CPU_CLK_HZ / 115200u);
  UART_CTRL = (baud_div << 16u) | UART_CTRL_TX_EN | UART_CTRL_RX_EN;
}

void th_timestamp(void) {
  uint32_t us = (uint32_t)(TIMER_LOW / (uint32_t)(CPU_CLK_HZ / 1000000ul));
  if (us == 0u) {
    us = 1u;
  }
  /* Use %u so the minimal UART formatter always matches varargs on RV32. */
  th_printf("m-lap-us-%u\r\n", us);
}

void th_timestamp_initialize(void) {
  th_printf(EE_MSG_TIMESTAMP_MODE);
  th_timestamp();
}

char th_getchar() {
  while (UART_STATUS & UART_STATUS_RX_EMPTY) {
  }
  return static_cast<char>(UART_RDATA & 0xffu);
}
