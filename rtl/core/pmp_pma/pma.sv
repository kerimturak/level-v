/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

================================================================================
CERES RISC-V — Physical Memory Attributes (PMA)
================================================================================
Description:
  Defines memory regions and their attributes for the memory subsystem.
  All peripheral regions are uncached and non-executable.

Memory Map:
  0x0000_0000 - 0x0FFF_FFFF : Debug Module (256MB) - Future
  0x1000_0000 - 0x1FFF_FFFF : Boot ROM (256MB) - Future
  0x2000_0000 - 0x2000_0FFF : UART0 (4KB)
  0x2000_1000 - 0x2000_1FFF : UART1 (4KB)
  0x2000_2000 - 0x2000_2FFF : SPI0 (4KB)
  0x2000_3000 - 0x2000_3FFF : I2C0 (4KB)
  0x2000_4000 - 0x2000_4FFF : GPIO (4KB)
  0x2000_5000 - 0x2000_5FFF : PWM (4KB)
  0x2000_6000 - 0x2000_6FFF : Timer (4KB)
  0x2000_7000 - 0x2000_7FFF : PLIC (4KB)
  0x2000_8000 - 0x2000_8FFF : Watchdog (4KB)
  0x2000_9000 - 0x2000_9FFF : DMA (4KB)
  0x2000_A000 - 0x2000_AFFF : Reserved (SPI1) (4KB) - Future
  0x2000_B000 - 0x2000_BFFF : Reserved (I2C1) (4KB) - Future
  0x2000_C000 - 0x2000_CFFF : Reserved (CRC) (4KB) - Future
  0x2000_D000 - 0x2000_DFFF : VGA Control (4KB)
  0x2000_E000 - 0x2000_EFFF : Reserved (RTC) (4KB) - Future
  0x2000_F000 - 0x2000_FFFF : Reserved (System Controller) (4KB) - Future
  0x2010_0000 - 0x2013_FFFF : VGA Framebuffer (256KB)
  0x3000_0000 - 0x3000_FFFF : CLINT (64KB)
  0x4000_0000 - 0x7FFF_FFFF : External Memory (1GB) - Future
  0x8000_0000 - 0xFFFF_FFFF : Main RAM (2GB)
================================================================================
*/
`timescale 1ns / 1ps
`include "ceres_defines.svh"

module pma
  import ceres_param::*;
(
    input logic [XLEN-1:0] addr_i,
    output logic uncached_o,
    output logic memregion_o,
    output logic grand_o
);

  // ===========================================================================
  // PMA Region Structure
  // ===========================================================================
  typedef struct packed {
    logic [XLEN-1:0] addr;       // Base address
    logic [XLEN-1:0] mask;       // Address mask (1 = ignore bit)
    logic            uncached;   // 1 = bypass cache
    logic            memregion;  // 1 = valid memory region
    logic            x;          // 1 = executable
    logic            w;          // 1 = writable
    logic            r;          // 1 = readable
  } pma_t;

  // ===========================================================================
  // Number of PMA Regions
  // ===========================================================================
  localparam int NUM_REGIONS = 20;

  logic [NUM_REGIONS-1:0] region_match;

  // ===========================================================================
  // PMA Region Definitions
  // ===========================================================================
  // Note: Mask bits set to 1 are ignored during address matching
  // Example: mask=0x0000_0FFF covers 4KB (bits [11:0] ignored)
  //          mask=0x0003_FFFF covers 256KB (bits [17:0] ignored)
  //          mask=0x7FFF_FFFF covers 2GB (bits [30:0] ignored)
  // ===========================================================================

  localparam pma_t [NUM_REGIONS-1:0] pma_map = '{
      // -----------------------------------------------------------------------
      // Main Memory - Cacheable, Executable
      // -----------------------------------------------------------------------
      // [0] RAM: 0x8000_0000 - 0xFFFF_FFFF (2GB max, typically 128KB-1MB used)
      '{
          addr: 32'h8000_0000,
          mask: 32'h7FFF_FFFF,
          uncached: 1'b0,
          memregion: 1'b1,
          x: 1'b1,
          w: 1'b1,
          r: 1'b1
      },

      // -----------------------------------------------------------------------
      // CLINT - Core Local Interruptor
      // -----------------------------------------------------------------------
      // [1] CLINT: 0x3000_0000 - 0x3000_FFFF (64KB)
      '{
          addr: 32'h3000_0000,
          mask: 32'h0000_FFFF,
          uncached: 1'b1,
          memregion: 1'b1,
          x: 1'b0,
          w: 1'b1,
          r: 1'b1
      },

      // -----------------------------------------------------------------------
      // Peripheral Region - All 4KB slots
      // -----------------------------------------------------------------------
      // [2] UART0: 0x2000_0000 - 0x2000_0FFF (4KB)
      '{
          addr: 32'h2000_0000,
          mask: 32'h0000_0FFF,
          uncached: 1'b1,
          memregion: 1'b1,
          x: 1'b0,
          w: 1'b1,
          r: 1'b1
      },

      // [3] UART1: 0x2000_1000 - 0x2000_1FFF (4KB)
      '{
          addr: 32'h2000_1000,
          mask: 32'h0000_0FFF,
          uncached: 1'b1,
          memregion: 1'b1,
          x: 1'b0,
          w: 1'b1,
          r: 1'b1
      },

      // [4] SPI0: 0x2000_2000 - 0x2000_2FFF (4KB)
      '{
          addr: 32'h2000_2000,
          mask: 32'h0000_0FFF,
          uncached: 1'b1,
          memregion: 1'b1,
          x: 1'b0,
          w: 1'b1,
          r: 1'b1
      },

      // [5] I2C0: 0x2000_3000 - 0x2000_3FFF (4KB)
      '{
          addr: 32'h2000_3000,
          mask: 32'h0000_0FFF,
          uncached: 1'b1,
          memregion: 1'b1,
          x: 1'b0,
          w: 1'b1,
          r: 1'b1
      },

      // [6] GPIO: 0x2000_4000 - 0x2000_4FFF (4KB)
      '{
          addr: 32'h2000_4000,
          mask: 32'h0000_0FFF,
          uncached: 1'b1,
          memregion: 1'b1,
          x: 1'b0,
          w: 1'b1,
          r: 1'b1
      },

      // [7] PWM: 0x2000_5000 - 0x2000_5FFF (4KB)
      '{
          addr: 32'h2000_5000,
          mask: 32'h0000_0FFF,
          uncached: 1'b1,
          memregion: 1'b1,
          x: 1'b0,
          w: 1'b1,
          r: 1'b1
      },

      // [8] Timer: 0x2000_6000 - 0x2000_6FFF (4KB)
      '{
          addr: 32'h2000_6000,
          mask: 32'h0000_0FFF,
          uncached: 1'b1,
          memregion: 1'b1,
          x: 1'b0,
          w: 1'b1,
          r: 1'b1
      },

      // [9] PLIC: 0x2000_7000 - 0x2000_7FFF (4KB)
      '{
          addr: 32'h2000_7000,
          mask: 32'h0000_0FFF,
          uncached: 1'b1,
          memregion: 1'b1,
          x: 1'b0,
          w: 1'b1,
          r: 1'b1
      },

      // [10] Watchdog: 0x2000_8000 - 0x2000_8FFF (4KB)
      '{
          addr: 32'h2000_8000,
          mask: 32'h0000_0FFF,
          uncached: 1'b1,
          memregion: 1'b1,
          x: 1'b0,
          w: 1'b1,
          r: 1'b1
      },

      // [11] DMA: 0x2000_9000 - 0x2000_9FFF (4KB)
      '{
          addr: 32'h2000_9000,
          mask: 32'h0000_0FFF,
          uncached: 1'b1,
          memregion: 1'b1,
          x: 1'b0,
          w: 1'b1,
          r: 1'b1
      },

      // [12] Reserved (SPI1): 0x2000_A000 - 0x2000_AFFF (4KB) - Future
      '{
          addr: 32'h2000_A000,
          mask: 32'h0000_0FFF,
          uncached: 1'b1,
          memregion: 1'b0,
          x: 1'b0,
          w: 1'b0,
          r: 1'b0
      },

      // [13] Reserved (I2C1): 0x2000_B000 - 0x2000_BFFF (4KB) - Future
      '{
          addr: 32'h2000_B000,
          mask: 32'h0000_0FFF,
          uncached: 1'b1,
          memregion: 1'b0,
          x: 1'b0,
          w: 1'b0,
          r: 1'b0
      },

      // [14] Reserved (CRC): 0x2000_C000 - 0x2000_CFFF (4KB) - Future
      '{
          addr: 32'h2000_C000,
          mask: 32'h0000_0FFF,
          uncached: 1'b1,
          memregion: 1'b0,
          x: 1'b0,
          w: 1'b0,
          r: 1'b0
      },

      // [15] VGA Control: 0x2000_D000 - 0x2000_DFFF (4KB)
      '{
          addr: 32'h2000_D000,
          mask: 32'h0000_0FFF,
          uncached: 1'b1,
          memregion: 1'b1,
          x: 1'b0,
          w: 1'b1,
          r: 1'b1
      },

      // [16] Reserved (RTC): 0x2000_E000 - 0x2000_EFFF (4KB) - Future
      '{
          addr: 32'h2000_E000,
          mask: 32'h0000_0FFF,
          uncached: 1'b1,
          memregion: 1'b0,
          x: 1'b0,
          w: 1'b0,
          r: 1'b0
      },

      // [17] Reserved (SysCtrl): 0x2000_F000 - 0x2000_FFFF (4KB) - Future
      '{
          addr: 32'h2000_F000,
          mask: 32'h0000_0FFF,
          uncached: 1'b1,
          memregion: 1'b0,
          x: 1'b0,
          w: 1'b0,
          r: 1'b0
      },

      // -----------------------------------------------------------------------
      // VGA Framebuffer - Large uncached region
      // -----------------------------------------------------------------------
      // [18] VGA Framebuffer: 0x2010_0000 - 0x2013_FFFF (256KB)
      '{
          addr: 32'h2010_0000,
          mask: 32'h0003_FFFF,
          uncached: 1'b1,
          memregion: 1'b1,
          x: 1'b0,
          w: 1'b1,
          r: 1'b1
      },

      // -----------------------------------------------------------------------
      // Future Regions (commented out, set memregion=0)
      // -----------------------------------------------------------------------
      // [19] External Memory: 0x4000_0000 - 0x7FFF_FFFF (1GB) - Future
      '{
          addr: 32'h4000_0000,
          mask: 32'h3FFF_FFFF,
          uncached: 1'b0,
          memregion: 1'b0,
          x: 1'b1,
          w: 1'b1,
          r: 1'b1
      }

  // Boot ROM: 0x1000_0000 - Requires separate entry when enabled
  // Debug Module: 0x0000_0000 - Requires separate entry when enabled
  };

  // ===========================================================================
  // Region Matching Logic
  // ===========================================================================
  for (genvar i = 0; i < NUM_REGIONS; i++) begin : gen_region_match
    assign region_match[i] = (pma_map[i].addr == (addr_i & ~pma_map[i].mask));
  end

  // ===========================================================================
  // Output Logic - Priority encoded (first match wins)
  // ===========================================================================
  always_comb begin
    memregion_o = 1'b0;
    uncached_o  = 1'b0;
    grand_o     = 1'b0;

    // Priority encoder - check regions in order
    // Use a casez on the match vector so synthesis tools don't need a 'break'
    // region_match[NUM_REGIONS-1:0] -> bit[19] is MSB, bit[0] is LSB (region 0)
    casez (region_match)
      20'b???????????????????1: begin
        uncached_o  = pma_map[0].uncached;
        memregion_o = pma_map[0].memregion;
        grand_o     = pma_map[0].x;
      end
      20'b??????????????????10: begin
        uncached_o  = pma_map[1].uncached;
        memregion_o = pma_map[1].memregion;
        grand_o     = pma_map[1].x;
      end
      20'b?????????????????100: begin
        uncached_o  = pma_map[2].uncached;
        memregion_o = pma_map[2].memregion;
        grand_o     = pma_map[2].x;
      end
      20'b????????????????1000: begin
        uncached_o  = pma_map[3].uncached;
        memregion_o = pma_map[3].memregion;
        grand_o     = pma_map[3].x;
      end
      20'b???????????????10000: begin
        uncached_o  = pma_map[4].uncached;
        memregion_o = pma_map[4].memregion;
        grand_o     = pma_map[4].x;
      end
      20'b??????????????100000: begin
        uncached_o  = pma_map[5].uncached;
        memregion_o = pma_map[5].memregion;
        grand_o     = pma_map[5].x;
      end
      20'b?????????????1000000: begin
        uncached_o  = pma_map[6].uncached;
        memregion_o = pma_map[6].memregion;
        grand_o     = pma_map[6].x;
      end
      20'b????????????10000000: begin
        uncached_o  = pma_map[7].uncached;
        memregion_o = pma_map[7].memregion;
        grand_o     = pma_map[7].x;
      end
      20'b???????????100000000: begin
        uncached_o  = pma_map[8].uncached;
        memregion_o = pma_map[8].memregion;
        grand_o     = pma_map[8].x;
      end
      20'b??????????1000000000: begin
        uncached_o  = pma_map[9].uncached;
        memregion_o = pma_map[9].memregion;
        grand_o     = pma_map[9].x;
      end
      20'b?????????10000000000: begin
        uncached_o  = pma_map[10].uncached;
        memregion_o = pma_map[10].memregion;
        grand_o     = pma_map[10].x;
      end
      20'b????????100000000000: begin
        uncached_o  = pma_map[11].uncached;
        memregion_o = pma_map[11].memregion;
        grand_o     = pma_map[11].x;
      end
      20'b???????1000000000000: begin
        uncached_o  = pma_map[12].uncached;
        memregion_o = pma_map[12].memregion;
        grand_o     = pma_map[12].x;
      end
      20'b??????10000000000000: begin
        uncached_o  = pma_map[13].uncached;
        memregion_o = pma_map[13].memregion;
        grand_o     = pma_map[13].x;
      end
      20'b?????100000000000000: begin
        uncached_o  = pma_map[14].uncached;
        memregion_o = pma_map[14].memregion;
        grand_o     = pma_map[14].x;
      end
      20'b????1000000000000000: begin
        uncached_o  = pma_map[15].uncached;
        memregion_o = pma_map[15].memregion;
        grand_o     = pma_map[15].x;
      end
      20'b???10000000000000000: begin
        uncached_o  = pma_map[16].uncached;
        memregion_o = pma_map[16].memregion;
        grand_o     = pma_map[16].x;
      end
      20'b??100000000000000000: begin
        uncached_o  = pma_map[17].uncached;
        memregion_o = pma_map[17].memregion;
        grand_o     = pma_map[17].x;
      end
      20'b?1000000000000000000: begin
        uncached_o  = pma_map[18].uncached;
        memregion_o = pma_map[18].memregion;
        grand_o     = pma_map[18].x;
      end
      20'b10000000000000000000: begin
        uncached_o  = pma_map[19].uncached;
        memregion_o = pma_map[19].memregion;
        grand_o     = pma_map[19].x;
      end
      default: begin
        // No match; keep defaults (already zeroed)
      end
    endcase
  end

endmodule
