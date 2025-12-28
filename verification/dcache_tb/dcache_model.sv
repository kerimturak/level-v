// =============================================================================
// DCache Reference Model
// =============================================================================
// This module implements a behavioral reference model of the dcache
// Used for comparison with RTL during verification
//
// Features:
// - 2-way set-associative cache
// - Write-back policy with dirty tracking
// - Pseudo-LRU replacement
// - Supports aligned and unaligned accesses
// =============================================================================

module dcache_model #(
  parameter int XLEN      = 32,
  parameter int NUM_WAY   = 2,
  parameter int NUM_SET   = 2,    // Minimum for testing
  parameter int BLK_SIZE  = 128,  // 128-bit cache line
  parameter int TAG_WIDTH = 19,   // For 32-bit address space
  parameter int IDX_WIDTH = 1,    // log2(NUM_SET) = log2(2) = 1
  parameter int BOFFSET   = 4     // log2(BLK_SIZE/8) = log2(16) = 4
) (
  input  logic clk_i,
  input  logic rst_ni
);

  // =========================================================================
  // Model Storage Arrays
  // =========================================================================

  typedef struct packed {
    logic                valid;
    logic [TAG_WIDTH-1:0] tag;
    logic [BLK_SIZE-1:0]  data;
  } cache_line_t;

  cache_line_t data_array [NUM_SET][NUM_WAY];
  logic        dirty_array[NUM_SET][NUM_WAY];
  logic [NUM_WAY-2:0] plru_array[NUM_SET];  // PLRU tree nodes

  // =========================================================================
  // Helper Functions
  // =========================================================================

  // Extract fields from address
  function automatic logic [TAG_WIDTH-1:0] get_tag(logic [XLEN-1:0] addr);
    return addr[XLEN-1:IDX_WIDTH+BOFFSET];
  endfunction

  function automatic logic [IDX_WIDTH-1:0] get_index(logic [XLEN-1:0] addr);
    return addr[IDX_WIDTH+BOFFSET-1:BOFFSET];
  endfunction

  function automatic logic [BOFFSET-1:0] get_offset(logic [XLEN-1:0] addr);
    return addr[BOFFSET-1:0];
  endfunction

  // Check if address hits in cache
  function automatic logic [NUM_WAY-1:0] check_hit(
    logic [XLEN-1:0] addr,
    output logic hit
  );
    logic [TAG_WIDTH-1:0] tag_req;
    logic [IDX_WIDTH-1:0] idx;
    logic [NUM_WAY-1:0] hit_vec;

    tag_req = get_tag(addr);
    idx = get_index(addr);
    hit = 1'b0;
    hit_vec = '0;

    for (int w = 0; w < NUM_WAY; w++) begin
      if (data_array[idx][w].valid && data_array[idx][w].tag == tag_req) begin
        hit_vec[w] = 1'b1;
        hit = 1'b1;
      end
    end

    return hit_vec;
  endfunction

  // PLRU: Get eviction way
  function automatic logic [NUM_WAY-1:0] get_evict_way(logic [IDX_WIDTH-1:0] idx);
    logic [NUM_WAY-1:0] way;
    logic node;

    if (NUM_WAY == 2) begin
      node = plru_array[idx][0];
      way = node ? 2'b01 : 2'b10;  // node=0 -> evict way-0, node=1 -> evict way-1
    end else begin
      // For higher associativity, implement full PLRU tree
      way = '0;
      way[0] = 1'b1;  // Default to way-0
    end

    return way;
  endfunction

  // PLRU: Update after access
  function automatic void update_plru(logic [IDX_WIDTH-1:0] idx, logic [NUM_WAY-1:0] way);
    if (NUM_WAY == 2) begin
      // For 2-way: single bit, 0=recently used way-0, 1=recently used way-1
      if (way[0]) begin
        plru_array[idx][0] = 1'b1;  // Accessed way-0, point to way-1 for next eviction
      end else if (way[1]) begin
        plru_array[idx][0] = 1'b0;  // Accessed way-1, point to way-0 for next eviction
      end
    end
  endfunction

  // =========================================================================
  // Model Operations
  // =========================================================================

  // Reset all arrays
  task reset_model();
    for (int s = 0; s < NUM_SET; s++) begin
      for (int w = 0; w < NUM_WAY; w++) begin
        data_array[s][w].valid = 1'b0;
        data_array[s][w].tag = '0;
        data_array[s][w].data = '0;
        dirty_array[s][w] = 1'b0;
      end
      plru_array[s] = '0;
    end
    $display("[MODEL] Reset complete - all arrays cleared");
  endtask

  // Fill cache line (on miss)
  task fill_line(
    input logic [XLEN-1:0]     addr,
    input logic [BLK_SIZE-1:0] data,
    input logic                mark_dirty  // true if this is a write
  );
    logic [TAG_WIDTH-1:0] tag;
    logic [IDX_WIDTH-1:0] idx;
    logic [NUM_WAY-1:0] evict_way, hit_vec;
    logic hit;
    int victim_way;

    tag = get_tag(addr);
    idx = get_index(addr);
    hit_vec = check_hit(addr, hit);

    if (hit) begin
      $display("[MODEL ERROR] fill_line called but address 0x%08x already in cache!", addr);
      return;
    end

    // Get eviction way
    evict_way = get_evict_way(idx);
    victim_way = evict_way[0] ? 0 : 1;

    // Check if writeback needed
    if (data_array[idx][victim_way].valid && dirty_array[idx][victim_way]) begin
      $display("[MODEL] Writeback needed: idx=%0d way=%0d addr=0x%08x",
        idx, victim_way, {data_array[idx][victim_way].tag, idx, {BOFFSET{1'b0}}});
    end

    // Fill the line
    data_array[idx][victim_way].valid = 1'b1;
    data_array[idx][victim_way].tag = tag;
    data_array[idx][victim_way].data = data;
    dirty_array[idx][victim_way] = mark_dirty;

    // Update PLRU
    update_plru(idx, evict_way);

    $display("[MODEL] Fill: addr=0x%08x idx=%0d way=%0d data=0x%032h dirty=%b",
      addr, idx, victim_way, data, mark_dirty);
  endtask

  // Write to cache line (on hit)
  task write_hit(
    input logic [XLEN-1:0] addr,
    input logic [31:0]     data,
    input logic [1:0]      size  // 0=byte, 1=half, 2=word
  );
    logic [TAG_WIDTH-1:0] tag;
    logic [IDX_WIDTH-1:0] idx;
    logic [NUM_WAY-1:0] hit_vec;
    logic hit;
    int hit_way;
    int byte_offset;
    logic [BLK_SIZE-1:0] line_data;

    tag = get_tag(addr);
    idx = get_index(addr);
    hit_vec = check_hit(addr, hit);

    if (!hit) begin
      $display("[MODEL ERROR] write_hit called but address 0x%08x not in cache!", addr);
      return;
    end

    // Find which way hit
    hit_way = hit_vec[0] ? 0 : 1;

    // Calculate byte offset within cache line
    byte_offset = get_offset(addr);

    // Update cache line data
    line_data = data_array[idx][hit_way].data;

    case (size)
      2'b00: begin  // Byte
        line_data[byte_offset*8 +: 8] = data[7:0];
      end
      2'b01: begin  // Halfword
        line_data[byte_offset*8 +: 16] = data[15:0];
      end
      2'b10: begin  // Word
        line_data[byte_offset*8 +: 32] = data[31:0];
      end
    endcase

    data_array[idx][hit_way].data = line_data;
    dirty_array[idx][hit_way] = 1'b1;

    // Update PLRU
    update_plru(idx, hit_vec);

    $display("[MODEL] Write: addr=0x%08x idx=%0d way=%0d data=0x%08x size=%0d",
      addr, idx, hit_way, data, size);
  endtask

  // Read from cache (on hit)
  task read_hit(
    input  logic [XLEN-1:0] addr,
    input  logic [1:0]      size,
    output logic [31:0]     data
  );
    logic [TAG_WIDTH-1:0] tag;
    logic [IDX_WIDTH-1:0] idx;
    logic [NUM_WAY-1:0] hit_vec;
    logic hit;
    int hit_way;
    int byte_offset;
    logic [BLK_SIZE-1:0] line_data;

    tag = get_tag(addr);
    idx = get_index(addr);
    hit_vec = check_hit(addr, hit);

    if (!hit) begin
      $display("[MODEL ERROR] read_hit called but address 0x%08x not in cache!", addr);
      data = 'x;
      return;
    end

    hit_way = hit_vec[0] ? 0 : 1;
    byte_offset = get_offset(addr);
    line_data = data_array[idx][hit_way].data;

    case (size)
      2'b00: data = {24'b0, line_data[byte_offset*8 +: 8]};
      2'b01: data = {16'b0, line_data[byte_offset*8 +: 16]};
      2'b10: data = line_data[byte_offset*8 +: 32];
      default: data = 'x;
    endcase

    // Update PLRU
    update_plru(idx, hit_vec);

    $display("[MODEL] Read: addr=0x%08x idx=%0d way=%0d data=0x%08x",
      addr, idx, hit_way, data);
  endtask

  // =========================================================================
  // Comparison Functions (to be called from testbench)
  // =========================================================================

  function automatic logic compare_arrays(
    input string rtl_path  // Hierarchical path to RTL dcache
  );
    logic match;
    match = 1'b1;

    // TODO: Add hierarchical access to compare with RTL
    // This will be implemented in testbench

    return match;
  endfunction

  // =========================================================================
  // Initialization
  // =========================================================================

  initial begin
    reset_model();
  end

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      reset_model();
    end
  end

endmodule
