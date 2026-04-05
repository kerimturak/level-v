/*
 * Auto-generated Hardware Definitions for level-V
 * ISA: RV32IMC_Zicsr
 * Generated from memory_map.yaml
 */

#ifndef _MEMORY_MAP_H_
#define _MEMORY_MAP_H_

#include <stdint.h>

/* ============================================================ */
/* Clock Configuration */
/* ============================================================ */
#define CPU_CLK              25000000UL    /* 25 MHz */
#define CLOCKS_PER_SEC       CPU_CLK
#define BAUD_RATE            115200

/* ============================================================ */
/* Memory Regions */
/* ============================================================ */
#define ROM_BASE             0x80000000
#define ROM_SIZE             0x00008000
#define RAM_BASE             0x80000000
#define RAM_SIZE             0x00010000
#define STACK_SIZE           0x00002000

/* ============================================================ */
/* UART Peripheral */
/* ============================================================ */
#define UART_BASE         0x20000000

#define UART_CTRL            (*(volatile uint32_t*)(0x20000000))  /*  */
#define UART_STATUS          (*(volatile uint32_t*)(0x20000004))  /*  */
#define UART_RDATA           (*(volatile uint32_t*)(0x20000008))  /*  */
#define UART_WDATA           (*(volatile uint32_t*)(0x2000000C))  /*  */

/* ============================================================ */
/* TIMER Peripheral */
/* ============================================================ */
#define TIMER_BASE         0x30000000

#define TIMER_LOW            (*(volatile uint32_t*)(0x30000000))  /*  */
#define TIMER_HIGH           (*(volatile uint32_t*)(0x30000004))  /*  */

/* UART Status Register Bits */
#define UART_STATUS_TX_FULL  (1 << 0)
#define UART_STATUS_RX_FULL  (1 << 1)
#define UART_STATUS_TX_EMPTY (1 << 2)
#define UART_STATUS_RX_EMPTY (1 << 3)

/* UART Control Register Bits */
#define UART_CTRL_TX_EN      (1 << 0)
#define UART_CTRL_RX_EN      (1 << 1)

#endif /* _MEMORY_MAP_H_ */
