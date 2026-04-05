/*
 * MLPerf Tiny — Level-V entry. Unattended Verilator run: one inference then idle.
 */
#include <cstddef>

#include "api/internally_implemented.h"
#include "api/submitter_implemented.h"

void ee_infer(size_t n, size_t n_warmup);

int main(int argc, char *argv[]) {
  (void)argc;
  (void)argv;

  ee_benchmark_initialize();
  ee_infer(1, 0);
  th_printf("m-mlperf-tiny-levelv-done\r\n");

  while (1) {
    __asm__ volatile("nop");
  }
}
