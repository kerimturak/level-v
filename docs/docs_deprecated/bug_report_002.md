# Bug Report #002: Unaligned Double Miss Duplicate Request

## Description
The CoreMark benchmark was hanging at address `0x800015de` (an unaligned instruction fetch). Investigation revealed that the processor was stuck in a loop or fetching incorrect data.

## Root Cause
The `align_buffer` module handles unaligned instruction fetches by splitting them into two cache line accesses (Even and Odd banks). In the case of a "double miss" (where both cache lines are missing from the cache), the `align_buffer` must request both lines from memory sequentially.

The state machine logic for sending the second request (for the Even bank) was flawed.
1. **Cycle 1 (First Response):** When the first response (Odd bank) arrived, the logic correctly asserted `lowX_req_o.valid` and updated the address to the second line.
2. **Cycle 2+ (Waiting):** In the subsequent cycles, while waiting for the second response, the logic *continued* to assert `lowX_req_o.valid`.

Since the memory wrapper (`ceres_wrapper` / `wrapper_ram`) treats a persistent `valid` signal as a new request (after the previous one is acknowledged), the memory system received **duplicate requests** for the second cache line. This likely caused the memory controller to return multiple responses or overwrite the data buffer with garbage, leading to instruction corruption and the observed hang.

## Fix
A new state register `waiting_second_q` was introduced to track the status of the second request.

- **Set:** When the first response arrives during a double miss (`miss_state == 2'b11` and `masked_valid`).
- **Clear:** When the second response arrives (`waiting_second_q` and `masked_valid`).

The `lowX_req_o.valid` signal is now suppressed if `waiting_second_q` is set, ensuring the request is sent exactly once.

### Code Change (`rtl/core/stage01_fetch/align_buffer.sv`)

```systemverilog
  // New state register
  logic waiting_second_q;

  always_ff @(posedge clk_i) begin
    if (!rst_ni | flush_i) begin
      waiting_second_q <= 1'b0;
    end else begin
      if ((miss_state == 2'b11) && masked_valid && unalign) begin
        waiting_second_q <= 1'b1;
      end else if (waiting_second_q && masked_valid) begin
        waiting_second_q <= 1'b0;
      end
    end
  end

  // Modified request logic
  // ...
    end else if (|miss_state) begin
      // Added !waiting_second_q to prevent duplicate requests
      lowX_req_o.valid = !buff_req_i.uncached && !masked_valid && !waiting_second_q;
    end else begin
  // ...
```

## Verification
- **Test:** `make run_verilator TEST_NAME=coremark`
- **Result:** The simulation no longer hangs at `0x800015de`. It successfully proceeds to execute the CoreMark benchmark (observed looping in `core_list_insert_new` and other functions).
