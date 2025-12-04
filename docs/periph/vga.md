# VGA Controller - Teknik Dokümantasyon

## İçindekiler

1. [Genel Bakış](#genel-bakış)
2. [Modül Arayüzü](#modül-arayüzü)
3. [VGA Timing](#vga-timing)
4. [Register Map](#register-map)
5. [Display Modları](#display-modları)
6. [Double Buffering](#double-buffering)

---

## Genel Bakış

### Amaç

`vga_controller` modülü, **640x480@60Hz VGA** video çıkışı sağlar. Text ve graphics modları, hardware cursor, palette RAM ve double buffering destekler.

### Dosya Konumu

```
rtl/periph/vga/vga_controller.sv
```

### Özellikler

- 640x480 @ 60Hz resolution
- 25.175 MHz pixel clock
- Text mode: 80x30 characters (8x16 font)
- Graphics modes: 1/2/4/8 bpp
- 256-color palette RAM
- Hardware cursor
- Double buffering
- Smooth scrolling
- Blanking interrupt

---

## Modül Arayüzü

### Port Tanımları

```systemverilog
module vga_controller
  import ceres_param::*;
#(
    parameter H_VISIBLE = 640,
    parameter H_FRONT   = 16,
    parameter H_SYNC    = 96,
    parameter H_BACK    = 48,
    parameter V_VISIBLE = 480,
    parameter V_FRONT   = 10,
    parameter V_SYNC    = 2,
    parameter V_BACK    = 33
) (
    input  logic clk_i,          // System clock
    input  logic rst_ni,

    // Pixel clock (25.175 MHz)
    input  logic pix_clk_i,

    // Register interface
    input  logic            stb_i,
    input  logic [     5:0] adr_i,
    input  logic [     3:0] byte_sel_i,
    input  logic            we_i,
    input  logic [XLEN-1:0] dat_i,
    output logic [XLEN-1:0] dat_o,

    // Frame buffer interface
    output logic [17:0] fb_addr_o,
    input  logic [ 7:0] fb_data_i,

    // VGA outputs
    output logic [7:0] vga_r_o,
    output logic [7:0] vga_g_o,
    output logic [7:0] vga_b_o,
    output logic       vga_hsync_o,
    output logic       vga_vsync_o,
    output logic       vga_blank_o,

    // Interrupt
    output logic vga_irq_o
);
```

### Timing Parameters

```systemverilog
// 640x480 @ 60Hz
localparam H_TOTAL   = H_VISIBLE + H_FRONT + H_SYNC + H_BACK;  // 800
localparam V_TOTAL   = V_VISIBLE + V_FRONT + V_SYNC + V_BACK;  // 525

// Pixel clock = 25.175 MHz
// Frame rate = 25.175M / (800 * 525) = 59.94 Hz
```

---

## VGA Timing

### Horizontal Timing

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        HORIZONTAL TIMING (per line)                      │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   ◄─────────────────── H_TOTAL (800 pixels) ───────────────────────►    │
│                                                                          │
│   ┌───────────────────────┬───────┬─────────┬─────────┐                 │
│   │      H_VISIBLE        │H_FRONT│ H_SYNC  │ H_BACK  │                 │
│   │        (640)          │ (16)  │  (96)   │  (48)   │                 │
│   └───────────────────────┴───────┴─────────┴─────────┘                 │
│                                                                          │
│   Pixel   0           639   640    655  656   751  752   799            │
│                                                                          │
│   HSYNC  ───────────────────────────┐         ┌─────────────            │
│                                     └─────────┘                          │
│                                      (active low)                        │
│                                                                          │
│   BLANK  ─────────────────────┐                         ┌───            │
│                               └─────────────────────────┘               │
│          │◄── visible ──►│◄────── blanking ─────────►│                  │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Vertical Timing

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        VERTICAL TIMING (per frame)                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   ◄─────────────────── V_TOTAL (525 lines) ────────────────────────►    │
│                                                                          │
│   ┌───────────────────────┬───────┬─────────┬─────────┐                 │
│   │      V_VISIBLE        │V_FRONT│ V_SYNC  │ V_BACK  │                 │
│   │        (480)          │ (10)  │   (2)   │  (33)   │                 │
│   └───────────────────────┴───────┴─────────┴─────────┘                 │
│                                                                          │
│   Line    0           479   480    489  490   491  492   524            │
│                                                                          │
│   VSYNC  ───────────────────────────┐     ┌─────────────────            │
│                                     └─────┘                              │
│                                    (active low)                          │
│                                                                          │
│   Frame rate = 25.175 MHz / (800 × 525) = 59.94 Hz                      │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Sync Generation Logic

```systemverilog
// Horizontal counter
always_ff @(posedge pix_clk_i) begin
    if (h_cnt == H_TOTAL - 1) begin
        h_cnt <= 0;
        if (v_cnt == V_TOTAL - 1)
            v_cnt <= 0;
        else
            v_cnt <= v_cnt + 1;
    end else begin
        h_cnt <= h_cnt + 1;
    end
end

// Sync signals (active low)
assign vga_hsync_o = ~(h_cnt >= H_VISIBLE + H_FRONT &&
                        h_cnt < H_VISIBLE + H_FRONT + H_SYNC);
assign vga_vsync_o = ~(v_cnt >= V_VISIBLE + V_FRONT &&
                        v_cnt < V_VISIBLE + V_FRONT + V_SYNC);
assign vga_blank_o = (h_cnt < H_VISIBLE) && (v_cnt < V_VISIBLE);
```

---

## Register Map

| Offset | Register | Açıklama |
|--------|----------|----------|
| 0x00 | CTRL | Control register |
| 0x04 | STATUS | Status register |
| 0x08 | FB_BASE | Frame buffer base address |
| 0x0C | CURSOR_X | Cursor X position |
| 0x10 | CURSOR_Y | Cursor Y position |
| 0x14 | CURSOR_CTRL | Cursor control |
| 0x18 | SCROLL_X | Horizontal scroll offset |
| 0x1C | SCROLL_Y | Vertical scroll offset |
| 0x20 | PALETTE[0] | Palette entry 0 |
| ... | ... | ... |
| 0x420 | PALETTE[255] | Palette entry 255 |

### CTRL Register

```
┌─────────────────────────────────────────────────────────────────────────┐
│ [7]   │ dbl_buf   │ Double buffer enable                                │
│ [6]   │ buf_sel   │ Active buffer select (0/1)                          │
│ [5:4] │ bpp       │ Bits per pixel (00=1, 01=2, 10=4, 11=8)             │
│ [3]   │ text_mode │ Text mode enable                                    │
│ [2]   │ irq_en    │ Vertical blank interrupt enable                     │
│ [1]   │ cursor_en │ Hardware cursor enable                              │
│ [0]   │ vga_en    │ VGA output enable                                   │
└─────────────────────────────────────────────────────────────────────────┘
```

### STATUS Register

```
┌─────────────────────────────────────────────────────────────────────────┐
│ [2] │ in_vblank  │ Currently in vertical blanking                       │
│ [1] │ in_hblank  │ Currently in horizontal blanking                     │
│ [0] │ vblank_irq │ Vertical blank interrupt flag (write 1 to clear)    │
└─────────────────────────────────────────────────────────────────────────┘
```

### CURSOR_CTRL Register

```
┌─────────────────────────────────────────────────────────────────────────┐
│ [15:8] │ cursor_color │ Cursor color (palette index)                    │
│ [4:0]  │ cursor_size  │ Cursor size (pixels)                            │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Display Modları

### Text Mode (80x30)

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        TEXT MODE                                         │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   Screen: 640 × 480 pixels                                              │
│   Font: 8 × 16 pixels per character                                     │
│   Characters: 80 columns × 30 rows = 2400 characters                    │
│                                                                          │
│   Frame Buffer Layout:                                                   │
│   ┌───────────────────────────────────────────────────────────┐         │
│   │ Offset  │ Content                                         │         │
│   ├─────────┼─────────────────────────────────────────────────┤         │
│   │ 0x0000  │ Character 0 (row 0, col 0)                      │         │
│   │ 0x0001  │ Attribute 0 (fg/bg color)                       │         │
│   │ 0x0002  │ Character 1 (row 0, col 1)                      │         │
│   │ 0x0003  │ Attribute 1                                     │         │
│   │ ...     │ ...                                              │         │
│   │ 0x009E  │ Character 79 (row 0, col 79)                    │         │
│   │ 0x009F  │ Attribute 79                                    │         │
│   │ 0x00A0  │ Character 80 (row 1, col 0)                     │         │
│   │ ...     │ ...                                              │         │
│   └─────────────────────────────────────────────────────────────┘       │
│                                                                          │
│   Attribute Byte:                                                        │
│   ┌───────┬───────┐                                                     │
│   │ [7:4] │ [3:0] │                                                     │
│   │  BG   │  FG   │                                                     │
│   └───────┴───────┘                                                     │
│                                                                          │
│   Memory: 80 × 30 × 2 = 4800 bytes                                      │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Graphics Modes

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        GRAPHICS MODES                                    │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   1 BPP (Monochrome):                                                   │
│   ────────────────────                                                   │
│   8 pixels per byte                                                      │
│   2 colors (palette index 0 and 1)                                      │
│   Memory: 640 × 480 / 8 = 38,400 bytes                                  │
│                                                                          │
│   Byte: [7][6][5][4][3][2][1][0]                                        │
│          │  │  │  │  │  │  │  └─ pixel 7                                │
│          │  │  │  │  │  │  └──── pixel 6                                │
│          └──┴──┴──┴──┴──┴─────── pixels 0-5                             │
│                                                                          │
│   2 BPP (4 colors):                                                      │
│   ────────────────────                                                   │
│   4 pixels per byte                                                      │
│   Memory: 640 × 480 / 4 = 76,800 bytes                                  │
│                                                                          │
│   Byte: [7:6][5:4][3:2][1:0]                                            │
│           │    │    │    └─ pixel 3                                     │
│           │    │    └────── pixel 2                                     │
│           │    └─────────── pixel 1                                     │
│           └──────────────── pixel 0                                     │
│                                                                          │
│   4 BPP (16 colors):                                                     │
│   ────────────────────                                                   │
│   2 pixels per byte                                                      │
│   Memory: 640 × 480 / 2 = 153,600 bytes                                 │
│                                                                          │
│   Byte: [7:4][3:0]                                                      │
│           │    └─ pixel 1 (4-bit palette index)                         │
│           └────── pixel 0 (4-bit palette index)                         │
│                                                                          │
│   8 BPP (256 colors):                                                    │
│   ────────────────────                                                   │
│   1 pixel per byte                                                       │
│   Memory: 640 × 480 = 307,200 bytes                                     │
│                                                                          │
│   Byte: [7:0] = palette index                                           │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Palette RAM

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        PALETTE RAM                                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   256 entries × 24 bits (RGB888)                                        │
│                                                                          │
│   ┌─────────┬─────────────────────────────────────────────────┐         │
│   │ Index   │ [23:16] R │ [15:8] G │ [7:0] B                  │         │
│   ├─────────┼─────────────────────────────────────────────────┤         │
│   │ 0       │ 0x000000 (black)                                │         │
│   │ 1       │ 0x0000AA (dark blue)                            │         │
│   │ 2       │ 0x00AA00 (dark green)                           │         │
│   │ 3       │ 0x00AAAA (dark cyan)                            │         │
│   │ 4       │ 0xAA0000 (dark red)                             │         │
│   │ 5       │ 0xAA00AA (dark magenta)                         │         │
│   │ 6       │ 0xAA5500 (brown)                                │         │
│   │ 7       │ 0xAAAAAA (light gray)                           │         │
│   │ 8       │ 0x555555 (dark gray)                            │         │
│   │ 9       │ 0x5555FF (blue)                                 │         │
│   │ 10      │ 0x55FF55 (green)                                │         │
│   │ 11      │ 0x55FFFF (cyan)                                 │         │
│   │ 12      │ 0xFF5555 (red)                                  │         │
│   │ 13      │ 0xFF55FF (magenta)                              │         │
│   │ 14      │ 0xFFFF55 (yellow)                               │         │
│   │ 15      │ 0xFFFFFF (white)                                │         │
│   │ 16-255  │ User-defined                                    │         │
│   └─────────┴─────────────────────────────────────────────────┘         │
│                                                                          │
│   Palette lookup:                                                        │
│   pixel_value → palette[pixel_value] → RGB output                       │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Double Buffering

### Konsept

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        DOUBLE BUFFERING                                  │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   Two frame buffers for tear-free animation:                            │
│                                                                          │
│   ┌─────────────────────┐     ┌─────────────────────┐                   │
│   │    Buffer 0         │     │    Buffer 1         │                   │
│   │                     │     │                     │                   │
│   │  ┌───────────────┐  │     │  ┌───────────────┐  │                   │
│   │  │               │  │     │  │               │  │                   │
│   │  │   Frame N     │◄─┼─────┼──│   Frame N+1   │  │                   │
│   │  │  (Display)    │  │ flip│  │   (Render)    │  │                   │
│   │  │               │  │     │  │               │  │                   │
│   │  └───────────────┘  │     │  └───────────────┘  │                   │
│   │                     │     │                     │                   │
│   └─────────────────────┘     └─────────────────────┘                   │
│                                                                          │
│   Workflow:                                                              │
│   1. Display reads from buffer 0                                        │
│   2. CPU renders to buffer 1                                            │
│   3. On VBlank, swap buffers (flip buf_sel)                             │
│   4. Display now reads buffer 1                                         │
│   5. CPU renders to buffer 0                                            │
│   6. Repeat...                                                           │
│                                                                          │
│   Buffer addresses:                                                      │
│   Buffer 0: FB_BASE                                                      │
│   Buffer 1: FB_BASE + frame_size                                        │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### VBlank Synchronization

```
              Frame N                    Frame N+1
         ◄────────────────►         ◄────────────────►
         
VSYNC  ─────┐         ┌─────────────┐         ┌──────
            └─────────┘             └─────────┘
            
VBLANK ────────────┐  │  ┌────────────────────┐  │  ┌──
            visible│  │  │     blanking       │  │  │
                   └──┘  └────────────────────┘──┘  └──
                      │              │
                      └──────────────┘
                         Safe swap window
                         (no tearing)
```

---

## Kullanım Örneği

### C Header

```c
#define VGA_BASE       0x2000D000

#define VGA_CTRL       (*(volatile uint32_t*)(VGA_BASE + 0x00))
#define VGA_STATUS     (*(volatile uint32_t*)(VGA_BASE + 0x04))
#define VGA_FB_BASE    (*(volatile uint32_t*)(VGA_BASE + 0x08))
#define VGA_CURSOR_X   (*(volatile uint32_t*)(VGA_BASE + 0x0C))
#define VGA_CURSOR_Y   (*(volatile uint32_t*)(VGA_BASE + 0x10))
#define VGA_CURSOR_CTRL (*(volatile uint32_t*)(VGA_BASE + 0x14))
#define VGA_SCROLL_X   (*(volatile uint32_t*)(VGA_BASE + 0x18))
#define VGA_SCROLL_Y   (*(volatile uint32_t*)(VGA_BASE + 0x1C))
#define VGA_PALETTE    ((volatile uint32_t*)(VGA_BASE + 0x20))

// CTRL bits
#define VGA_EN         (1 << 0)
#define VGA_CURSOR     (1 << 1)
#define VGA_IRQ_EN     (1 << 2)
#define VGA_TEXT_MODE  (1 << 3)
#define VGA_BPP_1      (0 << 4)
#define VGA_BPP_2      (1 << 4)
#define VGA_BPP_4      (2 << 4)
#define VGA_BPP_8      (3 << 4)
#define VGA_BUF_SEL    (1 << 6)
#define VGA_DBL_BUF    (1 << 7)

// STATUS bits
#define VGA_VBLANK_IRQ (1 << 0)
#define VGA_IN_HBLANK  (1 << 1)
#define VGA_IN_VBLANK  (1 << 2)

// Display parameters
#define VGA_WIDTH      640
#define VGA_HEIGHT     480
#define TEXT_COLS      80
#define TEXT_ROWS      30
```

### Text Mode Initialization

```c
#define FB_ADDR 0x80100000

void vga_text_init(void) {
    VGA_FB_BASE = FB_ADDR;
    VGA_CTRL = VGA_EN | VGA_TEXT_MODE | VGA_CURSOR;
    
    // Clear screen
    uint16_t *fb = (uint16_t*)FB_ADDR;
    for (int i = 0; i < TEXT_COLS * TEXT_ROWS; i++) {
        fb[i] = 0x0720;  // Space with gray on black
    }
}

void vga_putc(int x, int y, char c, uint8_t attr) {
    uint16_t *fb = (uint16_t*)FB_ADDR;
    fb[y * TEXT_COLS + x] = (attr << 8) | c;
}

void vga_puts(int x, int y, const char *s, uint8_t attr) {
    while (*s) {
        vga_putc(x++, y, *s++, attr);
        if (x >= TEXT_COLS) {
            x = 0;
            y++;
        }
    }
}
```

### Graphics Mode (8 BPP)

```c
void vga_graphics_init(void) {
    VGA_FB_BASE = FB_ADDR;
    VGA_CTRL = VGA_EN | VGA_BPP_8;
    
    // Setup default palette
    for (int i = 0; i < 256; i++) {
        // R3G3B2 format
        uint8_t r = ((i >> 5) & 0x7) * 36;
        uint8_t g = ((i >> 2) & 0x7) * 36;
        uint8_t b = (i & 0x3) * 85;
        VGA_PALETTE[i] = (r << 16) | (g << 8) | b;
    }
    
    // Clear to black
    memset((void*)FB_ADDR, 0, VGA_WIDTH * VGA_HEIGHT);
}

void vga_pixel(int x, int y, uint8_t color) {
    if (x < 0 || x >= VGA_WIDTH || y < 0 || y >= VGA_HEIGHT)
        return;
    uint8_t *fb = (uint8_t*)FB_ADDR;
    fb[y * VGA_WIDTH + x] = color;
}

void vga_line(int x0, int y0, int x1, int y1, uint8_t color) {
    // Bresenham's line algorithm
    int dx = abs(x1 - x0);
    int dy = abs(y1 - y0);
    int sx = x0 < x1 ? 1 : -1;
    int sy = y0 < y1 ? 1 : -1;
    int err = dx - dy;
    
    while (1) {
        vga_pixel(x0, y0, color);
        if (x0 == x1 && y0 == y1) break;
        int e2 = 2 * err;
        if (e2 > -dy) { err -= dy; x0 += sx; }
        if (e2 < dx)  { err += dx; y0 += sy; }
    }
}
```

### Double Buffering

```c
#define FB0_ADDR 0x80100000
#define FB1_ADDR 0x80200000  // FB0 + 640*480

static int current_buffer = 0;

void vga_init_double_buffer(void) {
    VGA_FB_BASE = FB0_ADDR;
    VGA_CTRL = VGA_EN | VGA_BPP_8 | VGA_DBL_BUF | VGA_IRQ_EN;
    current_buffer = 0;
}

void* vga_get_back_buffer(void) {
    return (void*)(current_buffer ? FB0_ADDR : FB1_ADDR);
}

void vga_swap_buffers(void) {
    // Wait for VBlank
    while (!(VGA_STATUS & VGA_IN_VBLANK));
    
    // Flip buffer
    current_buffer = !current_buffer;
    VGA_CTRL = (VGA_CTRL & ~VGA_BUF_SEL) | 
               (current_buffer ? VGA_BUF_SEL : 0);
}

// Animation loop
void game_loop(void) {
    while (1) {
        uint8_t *back = (uint8_t*)vga_get_back_buffer();
        
        // Clear back buffer
        memset(back, 0, VGA_WIDTH * VGA_HEIGHT);
        
        // Render frame
        render_scene(back);
        
        // Swap
        vga_swap_buffers();
    }
}
```

---

## Özet

`vga_controller` modülü:

1. **640x480@60Hz**: Standard VGA timing
2. **Text Mode**: 80x30 characters, 8x16 font
3. **Graphics**: 1/2/4/8 bpp color depths
4. **Palette**: 256 entry RGB palette RAM
5. **Cursor**: Hardware cursor support
6. **Double Buffer**: Tear-free animation
7. **Scrolling**: Smooth scroll offsets
8. **Interrupt**: VBlank synchronization
