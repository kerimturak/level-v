/* Fence.I writeback helper for dcache
   Extracted from dcache.sv to simplify main file and isolate FSM.
*/
module dcache_fencei #(
    parameter TAG_SIZE = 20,
    parameter BLK_SIZE = 128,
    parameter XLEN = 32,
    parameter NUM_WAY = 4,
    parameter IDX_WIDTH = 1,
    parameter BOFFSET = 4,
    parameter NUM_SET = 1
) (
    input logic                             clk_i,
    input logic                             rst_ni,
    input logic                             flush_i,
    input logic                             lowx_res_ready,
    input logic                             lowx_res_valid,
    input logic [NUM_WAY-1:0]               drsram_rd_rdirty,
    input logic [NUM_WAY-1:0][  TAG_SIZE:0] tsram_rtag,
    input logic [NUM_WAY-1:0][BLK_SIZE-1:0] dsram_rdata,

    output logic                 fi_active,
    output logic                 fi_writeback_req,
    output logic                 fi_mark_clean,
    output logic [ TAG_SIZE-1:0] fi_evict_tag,
    output logic [ BLK_SIZE-1:0] fi_evict_data,
    output logic [     XLEN-1:0] fi_evict_addr,
    output logic [  NUM_WAY-1:0] fi_way_onehot,
    output logic [IDX_WIDTH-1:0] fi_set_idx
);

  typedef enum logic [2:0] {
    FI_IDLE,
    FI_SCAN,
    FI_CHECK_WAY,
    FI_WRITEBACK_REQ,
    FI_WRITEBACK_WAIT,
    FI_MARK_CLEAN,
    FI_NEXT_WAY,
    FI_DONE
  } fencei_state_e;
  fencei_state_e fi_state_q, fi_state_d;

  logic [IDX_WIDTH-1:0] fi_set_idx_q, fi_set_idx_d;
  logic [$clog2(NUM_WAY)-1:0] fi_way_idx_q, fi_way_idx_d;
  logic flush_i_prev;

  // Detect rising edge
  always_ff @(posedge clk_i) begin
    if (!rst_ni) flush_i_prev <= 1'b0;
    else flush_i_prev <= flush_i;
  end

  wire fi_start = flush_i && !flush_i_prev && (fi_state_q == FI_IDLE);

  // one-hot current way
  always_comb begin
    fi_way_onehot = '0;
    fi_way_onehot[fi_way_idx_q] = 1'b1;
  end

  // check dirty: using tag valid bit stored at MSB of tag word
  wire fi_has_dirty = drsram_rd_rdirty[fi_way_idx_q] && tsram_rtag[fi_way_idx_q][TAG_SIZE];

  always_comb begin
    fi_evict_tag  = tsram_rtag[fi_way_idx_q][TAG_SIZE-1:0];
    fi_evict_data = dsram_rdata[fi_way_idx_q];
    fi_evict_addr = {fi_evict_tag, fi_set_idx_q, {BOFFSET{1'b0}}};
  end

  // FSM
  always_ff @(posedge clk_i) begin
    if (!rst_ni) begin
      fi_state_q   <= FI_IDLE;
      fi_set_idx_q <= '0;
      fi_way_idx_q <= '0;
    end else begin
      fi_state_q   <= fi_state_d;
      fi_set_idx_q <= fi_set_idx_d;
      fi_way_idx_q <= fi_way_idx_d;
    end
  end

  always_comb begin
    fi_state_d       = fi_state_q;
    fi_set_idx_d     = fi_set_idx_q;
    fi_way_idx_d     = fi_way_idx_q;
    fi_active        = 1'b0;
    fi_writeback_req = 1'b0;
    fi_mark_clean    = 1'b0;

    unique case (fi_state_q)
      FI_IDLE: begin
        if (fi_start) begin
          fi_state_d   = FI_SCAN;
          fi_set_idx_d = '0;
          fi_way_idx_d = '0;
          fi_active    = 1'b1;
        end
      end

      FI_SCAN: begin
        fi_active  = 1'b1;
        fi_state_d = FI_CHECK_WAY;
      end

      FI_CHECK_WAY: begin
        fi_active = 1'b1;
        if (fi_has_dirty) fi_state_d = FI_WRITEBACK_REQ;
        else fi_state_d = FI_NEXT_WAY;
      end

      FI_WRITEBACK_REQ: begin
        fi_active = 1'b1;
        fi_writeback_req = 1'b1;
        if (lowx_res_ready) fi_state_d = FI_WRITEBACK_WAIT;
      end

      FI_WRITEBACK_WAIT: begin
        fi_active = 1'b1;
        fi_writeback_req = 1'b1;
        if (lowx_res_valid) fi_state_d = FI_MARK_CLEAN;
      end

      FI_MARK_CLEAN: begin
        fi_active = 1'b1;
        fi_mark_clean = 1'b1;
        fi_state_d = FI_NEXT_WAY;
      end

      FI_NEXT_WAY: begin
        fi_active = 1'b1;
        if (fi_way_idx_q == $clog2(NUM_WAY)'(NUM_WAY - 1)) begin
          if (fi_set_idx_q == IDX_WIDTH'(NUM_SET - 1)) begin
            fi_state_d = FI_DONE;
          end else begin
            fi_set_idx_d = fi_set_idx_q + 1'b1;
            fi_way_idx_d = '0;
            fi_state_d   = FI_SCAN;
          end
        end else begin
          fi_way_idx_d = fi_way_idx_q + 1'b1;
          fi_state_d   = FI_CHECK_WAY;
        end
      end

      FI_DONE: begin
        fi_active = 1'b0;
        if (!flush_i) fi_state_d = FI_IDLE;
      end

      default: fi_state_d = FI_IDLE;
    endcase
  end

  assign fi_set_idx = fi_set_idx_q;

endmodule
