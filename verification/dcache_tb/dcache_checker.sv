// =============================================================================
// DCache Backdoor Checker
// =============================================================================
// Monitors internal DUT signals via hierarchical reference
// Compares against reference model
// Reports mismatches

module dcache_checker
  import ceres_param::*;
#(
  parameter string DUT_PATH = "tb_dcache.dut"
);

  // =========================================================================
  // Hierarchical Signal Access
  // =========================================================================

  // Access DUT internals via hierarchical path
  // Note: In SystemVerilog, we use $root to access from top level

  // Example checks (to be called from testbench)
  function automatic void check_tag_array(
    input int set_idx,
    input int way_idx,
    input logic expected_valid,
    input logic [18:0] expected_tag
  );
    logic actual_valid;
    logic [18:0] actual_tag;

    // TODO: Access via hierarchical reference
    // actual_valid = $root.tb_dcache.dut.tsram.rtag[way_idx][19];
    // actual_tag = $root.tb_dcache.dut.tsram.rtag[way_idx][18:0];

    // For now, placeholder
    $display("[CHECKER] Tag Array Check: set=%0d way=%0d", set_idx, way_idx);
    $display("          Expected: valid=%b tag=0x%05h", expected_valid, expected_tag);
    // $display("          Actual:   valid=%b tag=0x%05h", actual_valid, actual_tag);
  endfunction

  function automatic void check_dirty_bit(
    input int set_idx,
    input int way_idx,
    input logic expected_dirty
  );
    logic actual_dirty;

    // TODO: Access via hierarchical reference
    // actual_dirty = $root.tb_dcache.dut.dirty_reg[set_idx][way_idx];

    $display("[CHECKER] Dirty Bit Check: set=%0d way=%0d", set_idx, way_idx);
    $display("          Expected: dirty=%b", expected_dirty);
    // $display("          Actual:   dirty=%b", actual_dirty);
  endfunction

  function automatic void check_plru(
    input int set_idx,
    input logic expected_node
  );
    logic actual_node;

    // TODO: Access via hierarchical reference
    // For 2-way cache, PLRU is single bit
    // actual_node = $root.tb_dcache.dut.node_q[set_idx][0];

    $display("[CHECKER] PLRU Check: set=%0d", set_idx);
    $display("          Expected: node=%b", expected_node);
    // $display("          Actual:   node=%b", actual_node);
  endfunction

  function automatic void check_data_array(
    input int set_idx,
    input int way_idx,
    input logic [127:0] expected_data
  );
    logic [127:0] actual_data;

    // TODO: Access via hierarchical reference
    // actual_data = $root.tb_dcache.dut.dsram.rdata[way_idx];

    $display("[CHECKER] Data Array Check: set=%0d way=%0d", set_idx, way_idx);
    $display("          Expected: data=0x%032h", expected_data);
    // $display("          Actual:   data=0x%032h", actual_data);
  endfunction

  // =========================================================================
  // Complete Cache State Check
  // =========================================================================

  function automatic void check_cache_state(
    input string test_name
  );
    $display("\n[CHECKER] ========== Cache State Check: %s ==========", test_name);

    // Check all sets and ways
    for (int s = 0; s < 2; s++) begin
      for (int w = 0; w < 2; w++) begin
        $display("[CHECKER] Set=%0d Way=%0d:", s, w);
        // TODO: Read and display actual DUT values
        // check_tag_array(s, w, ...);
        // check_dirty_bit(s, w, ...);
        // check_data_array(s, w, ...);
      end
    end

    // Check PLRU state
    for (int s = 0; s < 2; s++) begin
      // check_plru(s, ...);
    end

    $display("[CHECKER] ==========================================\n");
  endfunction

endmodule
