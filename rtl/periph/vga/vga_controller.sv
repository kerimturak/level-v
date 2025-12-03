/*
Copyright (c) 2025 Kerim TURAK

Permission is granted to use, copy, modify, and distribute this software for any purpose,
with or without fee, provided that the above notice appears in all copies.

THE SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND.

================================================================================
VGA Controller Module
================================================================================
Description:
  Full-featured VGA controller for CERES SoC with:
  - Standard VGA timing (640x480 @ 60Hz, 25.175MHz pixel clock)
  - Configurable resolution support
  - Text mode (80x30 characters with 8x16 font)
  - Graphics mode (320x240 8-bit color or 640x480 1-bit)
  - Hardware cursor
  - Double buffering support
  - Smooth scrolling

  Memory Map (from VGA base 0x2000_A000):
    0x00: CTRL      - Control register
    0x04: STATUS    - Status register (read-only)
    0x08: HTIMING   - Horizontal timing
    0x0C: VTIMING   - Vertical timing
    0x10: FB_BASE   - Framebuffer base address
    0x14: FB_STRIDE - Framebuffer stride (bytes per line)
    0x18: CURSOR_X  - Cursor X position
    0x1C: CURSOR_Y  - Cursor Y position
    0x20: PALETTE   - Palette index
    0x24: COLOR     - Palette color data
    0x28: SCROLL_X  - Horizontal scroll offset
    0x2C: SCROLL_Y  - Vertical scroll offset

  CTRL Register [31:0]:
    [0]     : EN        - Display enable
    [1]     : MODE      - 0=Text mode, 1=Graphics mode
    [3:2]   : BPP       - Bits per pixel (00=1, 01=2, 10=4, 11=8)
    [4]     : CURSOR_EN - Hardware cursor enable
    [5]     : CURSOR_BL - Cursor blink enable
    [6]     : HSYNC_POL - HSync polarity (0=active low)
    [7]     : VSYNC_POL - VSync polarity (0=active low)
    [8]     : DBLBUF    - Double buffer enable
    [9]     : BUFSEL    - Active buffer select (for double buffering)
    [31:10] : Reserved

  Timing Parameters (for 640x480 @ 60Hz):
    Pixel Clock: 25.175 MHz
    H: 640 visible, 16 front porch, 96 sync, 48 back porch = 800 total
    V: 480 visible, 10 front porch, 2 sync, 33 back porch = 525 total
================================================================================
*/

`timescale 1ns / 1ps

module vga_controller
  import ceres_param::*;
#(
    // Display Resolution
    parameter int H_VISIBLE   = 640,
    parameter int H_FRONT     = 16,
    parameter int H_SYNC      = 96,
    parameter int H_BACK      = 48,
    parameter int V_VISIBLE   = 480,
    parameter int V_FRONT     = 10,
    parameter int V_SYNC      = 2,
    parameter int V_BACK      = 33,
    // Text Mode
    parameter int CHAR_WIDTH  = 8,
    parameter int CHAR_HEIGHT = 16,
    parameter int TEXT_COLS   = 80,
    parameter int TEXT_ROWS   = 30
) (
    // =========================================================================
    // Clock and Reset
    // =========================================================================
    input logic clk_i,        // System clock
    input logic pixel_clk_i,  // Pixel clock (25.175 MHz for 640x480)
    input logic rst_ni,

    // =========================================================================
    // Register Interface (System clock domain)
    // =========================================================================
    input  logic        stb_i,
    input  logic [ 5:0] adr_i,       // Word address [7:2]
    input  logic [ 3:0] byte_sel_i,
    input  logic        we_i,
    input  logic [31:0] dat_i,
    output logic [31:0] dat_o,

    // =========================================================================
    // Framebuffer Memory Interface (Pixel clock domain)
    // =========================================================================
    output logic        fb_req_o,
    output logic [31:0] fb_addr_o,
    input  logic [31:0] fb_data_i,
    input  logic        fb_ack_i,

    // =========================================================================
    // Character ROM Interface (for text mode)
    // =========================================================================
    output logic [11:0] char_addr_o,  // Character ROM address
    input  logic [ 7:0] char_data_i,  // Character bitmap row

    // =========================================================================
    // VGA Output Signals
    // =========================================================================
    output logic [3:0] vga_r_o,
    output logic [3:0] vga_g_o,
    output logic [3:0] vga_b_o,
    output logic       vga_hsync_o,
    output logic       vga_vsync_o,
    output logic       vga_de_o,     // Data enable (active during visible area)

    // =========================================================================
    // Interrupt
    // =========================================================================
    output logic vsync_irq_o  // Vertical sync interrupt
);

  // ===========================================================================
  // Timing Calculations
  // ===========================================================================
  localparam int H_TOTAL = H_VISIBLE + H_FRONT + H_SYNC + H_BACK;
  localparam int V_TOTAL = V_VISIBLE + V_FRONT + V_SYNC + V_BACK;

  localparam int H_SYNC_START = H_VISIBLE + H_FRONT;
  localparam int H_SYNC_END = H_SYNC_START + H_SYNC;
  localparam int V_SYNC_START = V_VISIBLE + V_FRONT;
  localparam int V_SYNC_END = V_SYNC_START + V_SYNC;

  // ===========================================================================
  // Register Addresses
  // ===========================================================================
  localparam logic [5:0] REG_CTRL = 6'h00;
  localparam logic [5:0] REG_STATUS = 6'h01;
  localparam logic [5:0] REG_HTIMING = 6'h02;
  localparam logic [5:0] REG_VTIMING = 6'h03;
  localparam logic [5:0] REG_FB_BASE = 6'h04;
  localparam logic [5:0] REG_FB_STRIDE = 6'h05;
  localparam logic [5:0] REG_CURSOR_X = 6'h06;
  localparam logic [5:0] REG_CURSOR_Y = 6'h07;
  localparam logic [5:0] REG_PALETTE = 6'h08;
  localparam logic [5:0] REG_COLOR = 6'h09;
  localparam logic [5:0] REG_SCROLL_X = 6'h0A;
  localparam logic [5:0] REG_SCROLL_Y = 6'h0B;

  // ===========================================================================
  // Control Registers (System clock domain)
  // ===========================================================================
  logic [31:0] ctrl_q;
  logic [31:0] fb_base_q;
  logic [15:0] fb_stride_q;
  logic [15:0] cursor_x_q;
  logic [15:0] cursor_y_q;
  logic [15:0] scroll_x_q;
  logic [15:0] scroll_y_q;
  logic [ 7:0] palette_idx_q;

  // Control bits extraction
  logic        disp_en;
  logic        gfx_mode;
  logic [ 1:0] bpp_mode;
  logic        cursor_en;
  logic        cursor_blink;
  logic        hsync_pol;
  logic        vsync_pol;
  logic        dbl_buf_en;
  logic        buf_sel;

  assign disp_en      = ctrl_q[0];
  assign gfx_mode     = ctrl_q[1];
  assign bpp_mode     = ctrl_q[3:2];
  assign cursor_en    = ctrl_q[4];
  assign cursor_blink = ctrl_q[5];
  assign hsync_pol    = ctrl_q[6];
  assign vsync_pol    = ctrl_q[7];
  assign dbl_buf_en   = ctrl_q[8];
  assign buf_sel      = ctrl_q[9];

  // ===========================================================================
  // Palette RAM (256 entries x 12-bit RGB)
  // ===========================================================================
  logic [11:0] palette_ram   [256];
  logic [11:0] palette_color;

  // Default VGA palette initialization
  initial begin
    // Basic 16 colors (CGA compatible)
    palette_ram[0]  = 12'h000;  // Black
    palette_ram[1]  = 12'h00A;  // Blue
    palette_ram[2]  = 12'h0A0;  // Green
    palette_ram[3]  = 12'h0AA;  // Cyan
    palette_ram[4]  = 12'hA00;  // Red
    palette_ram[5]  = 12'hA0A;  // Magenta
    palette_ram[6]  = 12'hA50;  // Brown
    palette_ram[7]  = 12'hAAA;  // Light Gray
    palette_ram[8]  = 12'h555;  // Dark Gray
    palette_ram[9]  = 12'h55F;  // Light Blue
    palette_ram[10] = 12'h5F5;  // Light Green
    palette_ram[11] = 12'h5FF;  // Light Cyan
    palette_ram[12] = 12'hF55;  // Light Red
    palette_ram[13] = 12'hF5F;  // Light Magenta
    palette_ram[14] = 12'hFF5;  // Yellow
    palette_ram[15] = 12'hFFF;  // White
    // Fill rest with grayscale ramp
    for (int i = 16; i < 256; i++) begin
      palette_ram[i] = {i[7:4], i[7:4], i[7:4]};
    end
  end

  // ===========================================================================
  // Timing Generator (Pixel clock domain)
  // ===========================================================================
  logic [11:0] h_cnt_q;
  logic [11:0] v_cnt_q;
  logic        h_visible;
  logic        v_visible;
  logic        h_sync_raw;
  logic        v_sync_raw;

  always_ff @(posedge pixel_clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      h_cnt_q <= 12'd0;
      v_cnt_q <= 12'd0;
    end else begin
      if (h_cnt_q >= H_TOTAL - 1) begin
        h_cnt_q <= 12'd0;
        if (v_cnt_q >= V_TOTAL - 1) begin
          v_cnt_q <= 12'd0;
        end else begin
          v_cnt_q <= v_cnt_q + 1;
        end
      end else begin
        h_cnt_q <= h_cnt_q + 1;
      end
    end
  end

  assign h_visible  = (h_cnt_q < H_VISIBLE);
  assign v_visible  = (v_cnt_q < V_VISIBLE);
  assign h_sync_raw = (h_cnt_q >= H_SYNC_START) && (h_cnt_q < H_SYNC_END);
  assign v_sync_raw = (v_cnt_q >= V_SYNC_START) && (v_cnt_q < V_SYNC_END);

  // Apply polarity
  assign vga_hsync_o = h_sync_raw ^ hsync_pol;
  assign vga_vsync_o = v_sync_raw ^ vsync_pol;
  assign vga_de_o    = h_visible & v_visible & disp_en;

  // ===========================================================================
  // VSync IRQ Generation (rising edge of vsync)
  // ===========================================================================
  logic v_sync_prev_q;
  logic vsync_irq_raw;

  always_ff @(posedge pixel_clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      v_sync_prev_q <= 1'b0;
    end else begin
      v_sync_prev_q <= v_sync_raw;
    end
  end

  assign vsync_irq_raw = v_sync_raw & ~v_sync_prev_q;

  // Synchronize to system clock
  logic vsync_sync_q, vsync_sync_qq;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      vsync_sync_q  <= 1'b0;
      vsync_sync_qq <= 1'b0;
    end else begin
      vsync_sync_q  <= vsync_irq_raw;
      vsync_sync_qq <= vsync_sync_q;
    end
  end
  assign vsync_irq_o = vsync_sync_q & ~vsync_sync_qq;

  // ===========================================================================
  // Pixel Coordinate with Scrolling
  // ===========================================================================
  logic [11:0] pixel_x;
  logic [11:0] pixel_y;

  assign pixel_x = h_cnt_q + scroll_x_q;
  assign pixel_y = v_cnt_q + scroll_y_q;

  // ===========================================================================
  // Framebuffer Address Generation
  // ===========================================================================
  logic [31:0] fb_offset;
  logic [31:0] active_fb_base;

  // Select active buffer
  assign active_fb_base = dbl_buf_en ? (buf_sel ? fb_base_q + (V_VISIBLE * fb_stride_q) : fb_base_q) : fb_base_q;

  always_comb begin
    if (gfx_mode) begin
      // Graphics mode
      case (bpp_mode)
        2'b00: fb_offset = (pixel_y * (fb_stride_q >> 3)) + (pixel_x >> 3);  // 1bpp
        2'b01: fb_offset = (pixel_y * (fb_stride_q >> 2)) + (pixel_x >> 2);  // 2bpp
        2'b10: fb_offset = (pixel_y * (fb_stride_q >> 1)) + (pixel_x >> 1);  // 4bpp
        2'b11: fb_offset = (pixel_y * fb_stride_q) + pixel_x;  // 8bpp
      endcase
    end else begin
      // Text mode: fetch character + attribute
      logic [7:0] char_col, char_row;
      char_col  = pixel_x[11:3];  // x / 8
      char_row  = pixel_y[11:4];  // y / 16
      fb_offset = (char_row * TEXT_COLS * 2) + (char_col * 2);  // 2 bytes per char
    end
  end

  assign fb_addr_o = active_fb_base + fb_offset;

  // ===========================================================================
  // Framebuffer Read Pipeline
  // ===========================================================================
  // Prefetch pixels ahead of display position
  logic [31:0] pixel_data_q;
  logic        prefetch_req;
  logic [ 2:0] prefetch_state;

  localparam PREFETCH_IDLE = 3'd0;
  localparam PREFETCH_REQ = 3'd1;
  localparam PREFETCH_WAIT = 3'd2;
  localparam PREFETCH_DONE = 3'd3;

  always_ff @(posedge pixel_clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      prefetch_state <= PREFETCH_IDLE;
      pixel_data_q   <= 32'h0;
    end else begin
      case (prefetch_state)
        PREFETCH_IDLE: begin
          if (h_visible && v_visible && disp_en) begin
            prefetch_state <= PREFETCH_REQ;
          end
        end
        PREFETCH_REQ: begin
          prefetch_state <= PREFETCH_WAIT;
        end
        PREFETCH_WAIT: begin
          if (fb_ack_i) begin
            pixel_data_q   <= fb_data_i;
            prefetch_state <= PREFETCH_DONE;
          end
        end
        PREFETCH_DONE: begin
          prefetch_state <= PREFETCH_IDLE;
        end
        default: prefetch_state <= PREFETCH_IDLE;
      endcase
    end
  end

  assign fb_req_o = (prefetch_state == PREFETCH_REQ);

  // ===========================================================================
  // Text Mode Character ROM Address
  // ===========================================================================
  logic [7:0] current_char;
  logic [3:0] char_line;

  assign current_char = pixel_data_q[7:0];
  assign char_line    = pixel_y[3:0];  // Line within character (0-15)
  assign char_addr_o  = {current_char, char_line};  // char * 16 + line

  // ===========================================================================
  // Pixel Color Generation
  // ===========================================================================
  logic [ 7:0] pixel_index;
  logic [11:0] pixel_color;
  logic [ 7:0] text_attr;
  logic        text_pixel;
  logic        cursor_active;

  // Text attribute byte: [7]=blink, [6:4]=bg color, [3:0]=fg color
  assign text_attr  = pixel_data_q[15:8];

  // Get pixel from character bitmap
  assign text_pixel = char_data_i[7-pixel_x[2:0]];

  // Hardware cursor
  logic [31:0] blink_cnt;
  logic        blink_phase;

  always_ff @(posedge pixel_clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      blink_cnt   <= 32'd0;
      blink_phase <= 1'b0;
    end else begin
      if (blink_cnt >= 25175000 / 2) begin  // ~0.5 sec blink
        blink_cnt   <= 32'd0;
        blink_phase <= ~blink_phase;
      end else begin
        blink_cnt <= blink_cnt + 1;
      end
    end
  end

  assign cursor_active = cursor_en && (pixel_x[11:3] == cursor_x_q[7:0]) && (pixel_y[11:4] == cursor_y_q[7:0]) && (pixel_y[3:0] >= 14) &&  // Bottom 2 lines
      (!cursor_blink || blink_phase);

  always_comb begin
    if (!disp_en || !vga_de_o) begin
      pixel_color = 12'h000;  // Blank
    end else if (gfx_mode) begin
      // Graphics mode
      case (bpp_mode)
        2'b00: pixel_index = pixel_data_q[pixel_x[4:0]] ? 8'hFF : 8'h00;
        2'b01: pixel_index = {6'b0, pixel_data_q[pixel_x[3:0]*2+:2]};
        2'b10: pixel_index = {4'b0, pixel_data_q[pixel_x[2:0]*4+:4]};
        2'b11: pixel_index = pixel_data_q[7:0];
      endcase
      pixel_color = palette_ram[pixel_index];
    end else begin
      // Text mode
      logic [3:0] fg_color, bg_color;
      fg_color = text_attr[3:0];
      bg_color = text_attr[6:4];

      if (cursor_active) begin
        // Invert colors at cursor
        pixel_color = text_pixel ? palette_ram[bg_color] : palette_ram[fg_color];
      end else begin
        pixel_color = text_pixel ? palette_ram[fg_color] : palette_ram[bg_color];
      end
    end
  end

  // Output RGB
  assign vga_r_o = pixel_color[11:8];
  assign vga_g_o = pixel_color[7:4];
  assign vga_b_o = pixel_color[3:0];

  // ===========================================================================
  // Register Write Logic (System clock domain)
  // ===========================================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ctrl_q        <= 32'h0;
      fb_base_q     <= 32'h8010_0000;  // Default FB at RAM + 1MB
      fb_stride_q   <= H_VISIBLE;
      cursor_x_q    <= 16'd0;
      cursor_y_q    <= 16'd0;
      scroll_x_q    <= 16'd0;
      scroll_y_q    <= 16'd0;
      palette_idx_q <= 8'd0;
    end else if (stb_i && we_i) begin
      case (adr_i)
        REG_CTRL: begin
          if (byte_sel_i[0]) ctrl_q[7:0] <= dat_i[7:0];
          if (byte_sel_i[1]) ctrl_q[15:8] <= dat_i[15:8];
          if (byte_sel_i[2]) ctrl_q[23:16] <= dat_i[23:16];
          if (byte_sel_i[3]) ctrl_q[31:24] <= dat_i[31:24];
        end
        REG_FB_BASE: begin
          if (byte_sel_i[0]) fb_base_q[7:0] <= dat_i[7:0];
          if (byte_sel_i[1]) fb_base_q[15:8] <= dat_i[15:8];
          if (byte_sel_i[2]) fb_base_q[23:16] <= dat_i[23:16];
          if (byte_sel_i[3]) fb_base_q[31:24] <= dat_i[31:24];
        end
        REG_FB_STRIDE: begin
          if (byte_sel_i[0]) fb_stride_q[7:0] <= dat_i[7:0];
          if (byte_sel_i[1]) fb_stride_q[15:8] <= dat_i[15:8];
        end
        REG_CURSOR_X: begin
          if (byte_sel_i[0]) cursor_x_q[7:0] <= dat_i[7:0];
          if (byte_sel_i[1]) cursor_x_q[15:8] <= dat_i[15:8];
        end
        REG_CURSOR_Y: begin
          if (byte_sel_i[0]) cursor_y_q[7:0] <= dat_i[7:0];
          if (byte_sel_i[1]) cursor_y_q[15:8] <= dat_i[15:8];
        end
        REG_PALETTE: begin
          if (byte_sel_i[0]) palette_idx_q <= dat_i[7:0];
        end
        REG_COLOR: begin
          palette_ram[palette_idx_q] <= dat_i[11:0];
        end
        REG_SCROLL_X: begin
          if (byte_sel_i[0]) scroll_x_q[7:0] <= dat_i[7:0];
          if (byte_sel_i[1]) scroll_x_q[15:8] <= dat_i[15:8];
        end
        REG_SCROLL_Y: begin
          if (byte_sel_i[0]) scroll_y_q[7:0] <= dat_i[7:0];
          if (byte_sel_i[1]) scroll_y_q[15:8] <= dat_i[15:8];
        end
        default: ;
      endcase
    end
  end

  // ===========================================================================
  // Register Read Logic
  // ===========================================================================
  always_comb begin
    dat_o = 32'h0;
    if (stb_i && !we_i) begin
      case (adr_i)
        REG_CTRL:      dat_o = ctrl_q;
        REG_STATUS:    dat_o = {20'h0, v_cnt_q};
        REG_HTIMING:   dat_o = {4'h0, H_TOTAL[11:0], 4'h0, H_VISIBLE[11:0]};
        REG_VTIMING:   dat_o = {4'h0, V_TOTAL[11:0], 4'h0, V_VISIBLE[11:0]};
        REG_FB_BASE:   dat_o = fb_base_q;
        REG_FB_STRIDE: dat_o = {16'h0, fb_stride_q};
        REG_CURSOR_X:  dat_o = {16'h0, cursor_x_q};
        REG_CURSOR_Y:  dat_o = {16'h0, cursor_y_q};
        REG_PALETTE:   dat_o = {24'h0, palette_idx_q};
        REG_COLOR:     dat_o = {20'h0, palette_ram[palette_idx_q]};
        REG_SCROLL_X:  dat_o = {16'h0, scroll_x_q};
        REG_SCROLL_Y:  dat_o = {16'h0, scroll_y_q};
        default:       dat_o = 32'h0;
      endcase
    end
  end

endmodule
