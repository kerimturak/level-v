/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.
*/

`timescale 1ns / 1ps

// ============================================================================
// ID Allocator: Free list based ID allocation for cache requests
// ============================================================================
// This module manages a free list of IDs that can be allocated to outgoing
// cache requests and deallocated when responses are received.
//
// Parameters:
//   NUM_IDS    - Number of IDs to manage (must be power of 2)
//   ID_WIDTH   - Width of ID field in bits (log2(NUM_IDS))
//   ID_PREFIX  - MSB bits to use as prefix for all allocated IDs
//
// Operation:
//   - Allocation: When alloc_i is high and an ID is available, allocate it
//   - Deallocation: When dealloc_i is high, return the ID to free list
//   - available_o indicates if any IDs are free
//
// Example usage:
//   - ICache: NUM_IDS=8, ID_PREFIX=4'b1xxx (MSB=1 indicates icache)
//   - DCache: NUM_IDS=8, ID_PREFIX=4'b0xxx (MSB=0 indicates dcache)
// ============================================================================

module id_allocator #(
    parameter int NUM_IDS = 8,
    parameter int ID_WIDTH = 4,
    parameter logic [ID_WIDTH-1:0] ID_PREFIX = 4'b1000  // Default: icache prefix
) (
    input  logic                 clk_i,
    input  logic                 rst_ni,
    // Allocation interface
    input  logic                 alloc_i,      // Request to allocate an ID
    output logic [ID_WIDTH-1:0]  id_o,         // Allocated ID
    output logic                 available_o,  // At least one ID available
    // Deallocation interface
    input  logic                 dealloc_i,    // Request to deallocate an ID
    input  logic [ID_WIDTH-1:0]  dealloc_id_i  // ID to deallocate
);

  localparam int LIST_SIZE = NUM_IDS;
  localparam int PTR_WIDTH = $clog2(LIST_SIZE);

  // Free list storage: holds available IDs
  logic [ID_WIDTH-1:0] free_list[LIST_SIZE];

  // Head pointer: points to next ID to allocate
  logic [PTR_WIDTH-1:0] head_ptr;

  // Tail pointer: points to next slot for deallocation
  logic [PTR_WIDTH-1:0] tail_ptr;

  // Counter for number of free IDs
  logic [PTR_WIDTH:0] free_count;

  // Extract lower bits from prefix to determine starting index
  localparam logic [PTR_WIDTH-1:0] PREFIX_OFFSET = ID_PREFIX[PTR_WIDTH-1:0];

  // Available signal: true if at least one ID is free
  assign available_o = (free_count > 0);

  // Output the next available ID
  assign id_o = free_list[head_ptr];

  // Sequential logic for allocation and deallocation
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      // Initialize free list with all IDs
      for (int i = 0; i < LIST_SIZE; i++) begin
        // Combine prefix MSBs with incrementing LSBs
        free_list[i] <= ID_PREFIX | ID_WIDTH'(i);
      end
      head_ptr   <= '0;
      tail_ptr   <= PTR_WIDTH'(LIST_SIZE - 1);
      free_count <= (PTR_WIDTH+1)'(LIST_SIZE);
    end else begin
      // Handle simultaneous allocation and deallocation
      case ({
        alloc_i && available_o, dealloc_i
      })
        2'b10: begin
          // Allocation only
          head_ptr   <= head_ptr + 1'b1;
          free_count <= free_count - 1'b1;
        end
        2'b01: begin
          // Deallocation only
          tail_ptr               <= tail_ptr + 1'b1;
          free_list[tail_ptr+1'b1] <= dealloc_id_i;
          free_count             <= free_count + 1'b1;
        end
        2'b11: begin
          // Both allocation and deallocation: pointers move but count stays same
          head_ptr               <= head_ptr + 1'b1;
          tail_ptr               <= tail_ptr + 1'b1;
          free_list[tail_ptr+1'b1] <= dealloc_id_i;
          // free_count stays the same
        end
        default: begin
          // No allocation or deallocation
        end
      endcase
    end
  end

  // Assertions for debugging (synthesis-time checks disabled in production)
`ifdef SIMULATION
  initial begin
    if (LIST_SIZE != NUM_IDS) begin
      $error("LIST_SIZE must equal NUM_IDS");
    end
    if ((1 << PTR_WIDTH) < LIST_SIZE) begin
      $error("PTR_WIDTH too small for LIST_SIZE");
    end
  end

  // Runtime assertions
  always_ff @(posedge clk_i) begin
    if (rst_ni) begin
      // Check for allocation when no IDs available
      if (alloc_i && !available_o) begin
        $warning("Allocation requested but no IDs available");
      end
      // Check for deallocation of invalid ID
      if (dealloc_i) begin
        // Verify ID has correct prefix
        if ((dealloc_id_i & ~ID_WIDTH'(LIST_SIZE - 1)) != (ID_PREFIX & ~ID_WIDTH'(LIST_SIZE - 1))) begin
          $error("Deallocation of ID with incorrect prefix: %0h (expected prefix: %0h)", dealloc_id_i, ID_PREFIX);
        end
      end
    end
  end
`endif

endmodule
