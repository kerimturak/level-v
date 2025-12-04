# CS_REG_FILE (CSR Register File) Modülü - Teknik Döküman

## Genel Bakış

`cs_reg_file.sv` modülü, RISC-V işlemcisinin **Control and Status Register** (CSR) file'ıdır. Machine-mode (M-mode) CSR'larını implement eder, trap handling, interrupt management, performance counters ve debug trigger register'larını içerir.

## RISC-V Privileged Levels

Bu implementasyon **M-mode only** (Machine Mode) destekler:

| Level | Encoding | Name | Privilege |
|-------|----------|------|-----------|
| M | 3 (0b11) | Machine | Highest (full access) |
| S | 1 (0b01) | Supervisor | Not implemented |
| U | 0 (0b00) | User | Not implemented |

**Rationale:** Embedded systems ve bare-metal uygulamalar için M-mode yeterlidir.

## Port Tanımları

### Clock & Control

| Port | Tip | Açıklama |
|------|-----|----------|
| `clk_i` | logic | Sistem clock'u |
| `rst_ni` | logic | Aktif-düşük asenkron reset |
| `stall_i` | stall_e | Pipeline stall sinyali |

### CSR Read/Write Interface

| Port | Tip | Açıklama |
|------|-----|----------|
| `rd_en_i` | logic | CSR read enable |
| `wr_en_i` | logic | CSR write enable |
| `csr_idx_i` | [11:0] | CSR address (12-bit CSR space) |
| `csr_wdata_i` | [XLEN-1:0] | Write data (from ALU) |
| `csr_rdata_o` | [XLEN-1:0] | Read data (to ALU) |

### Trap Interface

| Port | Tip | Açıklama |
|------|-----|----------|
| `trap_active_i` | logic | Trap active (exception/interrupt) |
| `de_trap_active_i` | logic | Decode stage trap active |
| `trap_cause_i` | [XLEN-1:0] | Exception/interrupt cause code |
| `trap_mepc_i` | [XLEN-1:0] | Exception PC (saved to mepc) |
| `trap_tval_i` | [XLEN-1:0] | Trap value (faulting instruction/address) |
| `instr_type_i` | instr_type_e | Instruction type (for MRET detection) |

### Interrupt Inputs (Hardware)

| Port | Tip | Açıklama |
|------|-----|----------|
| `timer_irq_i` | logic | CLINT timer interrupt (MTIP) |
| `sw_irq_i` | logic | CLINT software interrupt (MSIP) |
| `ext_irq_i` | logic | PLIC external interrupt (MEIP) |

### Outputs

| Port | Tip | Açıklama |
|------|-----|----------|
| `mtvec_o` | [XLEN-1:0] | Trap vector base address |
| `mepc_o` | [XLEN-1:0] | Exception PC (for MRET) |
| `misa_c_o` | logic | MISA.C bit (compressed extension enable) |
| `tdata1_o` | [XLEN-1:0] | Debug trigger data 1 |
| `tdata2_o` | [XLEN-1:0] | Debug trigger data 2 (breakpoint address) |
| `tcontrol_o` | [XLEN-1:0] | Debug trigger control |

## Implemented CSRs

### Machine Information Registers (Read-Only)

| Address | Name | Description | Value |
|---------|------|-------------|-------|
| 0xF11 | mvendorid | Vendor ID | 0 (not registered) |
| 0xF12 | marchid | Architecture ID | 5 (Spike compatible) |
| 0xF13 | mimpid | Implementation ID | 0 |
| 0xF14 | mhartid | Hardware thread ID | 0 (single-core) |
| 0xF15 | mconfigptr | Configuration pointer | 0 (not used) |

### Machine Trap Setup

| Address | Name | Description | R/W |
|---------|------|-------------|-----|
| 0x300 | mstatus | Machine status register | R/W |
| 0x301 | misa | ISA configuration | R/W (WARL) |
| 0x304 | mie | Machine interrupt enable | R/W |
| 0x305 | mtvec | Trap vector base address | R/W |
| 0x306 | mcounteren | Counter enable (S/U mode) | RO-0 |
| 0x310 | mstatush | Status register (upper 32 bits, RV32) | RO-0 |

### Machine Trap Handling

| Address | Name | Description | R/W |
|---------|------|-------------|-----|
| 0x340 | mscratch | Scratch register for trap handlers | R/W |
| 0x341 | mepc | Exception program counter | R/W |
| 0x342 | mcause | Exception cause | R/W |
| 0x343 | mtval | Trap value (faulting instruction/address) | R/W |
| 0x344 | mip | Machine interrupt pending | RO |

### Machine Counter/Timers

| Address | Name | Description | R/W |
|---------|------|-------------|-----|
| 0xB00 | mcycle | Cycle counter (lower 32 bits) | R/W |
| 0xB02 | minstret | Instruction counter (lower 32 bits) | R/W |
| 0xB80 | mcycleh | Cycle counter (upper 32 bits) | R/W |
| 0xB82 | minstreth | Instruction counter (upper 32 bits) | R/W |

### User-Mode Counter Shadows (Read-Only)

| Address | Name | Description | Value |
|---------|------|-------------|-------|
| 0xC00 | cycle | Cycle counter (alias to mcycle) | = mcycle |
| 0xC02 | instret | Instruction counter (alias to minstret) | = minstret |
| 0xC80 | cycleh | Cycle counter upper (alias to mcycleh) | = mcycleh |
| 0xC82 | instreth | Instruction counter upper (alias to minstreth) | = minstreth |

### Debug/Trigger Registers

| Address | Name | Description | R/W |
|---------|------|-------------|-----|
| 0x7A0 | tselect | Trigger select | RO-0 |
| 0x7A1 | tdata1 | Trigger data 1 (type, config) | R/W |
| 0x7A2 | tdata2 | Trigger data 2 (breakpoint address) | R/W |
| 0x7A3 | tdata3 | Trigger data 3 | RO-0 |
| 0x7A5 | tcontrol | Trigger control (MTE, MPTE) | R/W |

### Physical Memory Protection (Stub)

| Address | Name | Description | R/W |
|---------|------|-------------|-----|
| 0x3A0 | pmpcfg0 | PMP configuration | R/W |
| 0x3B0 | pmpaddr0 | PMP address | R/W |

**Not:** PMP henüz tam implement edilmemiş (stub)

## CSR Details

### mstatus (Machine Status Register)

```systemverilog
typedef struct packed {
  logic       mie;   // Machine Interrupt Enable
  logic       mpie;  // Previous MIE (saved during trap)
  logic [1:0] mpp;   // Previous Privilege Mode (always 2'b11 for M-mode)
} mstatus_t;
```

**Bit Layout:**
```
31              8 7    4 3    0
+---------------+------+------+
| (reserved=0)  | MPIE | MIE  |
+---------------+------+------+
                   ↑      ↑
                  bit 7  bit 3
```

**Fields:**
- **MIE (bit 3)**: Global interrupt enable (0 = disabled, 1 = enabled)
- **MPIE (bit 7)**: Previous MIE value (saved on trap entry)
- **MPP (bits 12:11)**: Previous privilege mode (hardwired to 0b11 = M-mode)

**Pack/Unpack Functions:**
```systemverilog
function automatic logic [31:0] pack_mstatus(mstatus_t m);
  logic [31:0] d = 32'd0;
  d[3] = m.mie;
  d[7] = m.mpie;
  d[12:11] = m.mpp;
  return d;
endfunction

function automatic mstatus_t unpack_mstatus(logic [31:0] d);
  return '{mie: d[3], mpie: d[7], mpp: 2'b11};  // MPP WARL (always M-mode)
endfunction
```

**Trap Entry:**
```systemverilog
mstatus.mpie <= mstatus.mie;  // Save current MIE
mstatus.mie <= 1'b0;          // Disable interrupts
mstatus.mpp <= 2'b11;         // M-mode
```

**MRET (Trap Return):**
```systemverilog
mstatus.mie <= mstatus.mpie;  // Restore previous MIE
mstatus.mpie <= 1'b1;         // Set MPIE to 1 (convention)
mstatus.mpp <= 2'b11;         // Remain in M-mode
```

### misa (ISA Configuration)

```systemverilog
typedef struct packed {
  logic [1:0] MXL;       // Machine XLEN (01 = RV32)
  logic [3:0] RESERVED;
  logic       Z, Y, X, W, V, U, T, S, R, Q, P, O, N, M, L, K, J, I, H, G, F, E, D, C, B, A;
} misa_ext_t;
```

**Ceres Configuration (RV32IMC):**
```
MXL = 2'b01   (RV32)
I = 1         (Base integer)
M = 1         (Multiply/Divide)
C = 1         (Compressed instructions)
```

**WARL (Write-Any-Read-Legal):**
- Only **C** extension bit is writable
- Allows runtime enable/disable of compressed instructions
- Other bits are read-only

**Writable Mask:**
```systemverilog
localparam logic [XLEN-1:0] MISA_WRITABLE_MASK = 32'h0000_0004;  // Bit 2 (C)
```

### mie (Machine Interrupt Enable)

```systemverilog
logic [XLEN-1:0] mie;
```

**Bit Layout:**
```
31       12 11  8 7   4 3   0
+-----------+----+-----+----+
| (reserved)| ME | MT  | MS |
+-----------+----+-----+----+
             ↑    ↑     ↑
          bit 11 bit 7 bit 3
```

**Fields:**
- **MSIE (bit 3)**: Machine Software Interrupt Enable
- **MTIE (bit 7)**: Machine Timer Interrupt Enable
- **MEIE (bit 11)**: Machine External Interrupt Enable

**Writable Mask:**
```systemverilog
localparam logic [XLEN-1:0] MIE_RW_MASK = 32'h0000_0888;  // Bits 3, 7, 11
```

**Interrupt Enable Logic:**
```
Interrupt Taken = mstatus.MIE && mie[cause] && mip[cause]
```

### mip (Machine Interrupt Pending)

```systemverilog
always_comb begin
  mip = '0;
  mip[3] = sw_irq_i;      // MSIP (Software Interrupt Pending)
  mip[7] = timer_irq_i;   // MTIP (Timer Interrupt Pending)
  mip[11] = ext_irq_i;    // MEIP (External Interrupt Pending)
end
```

**Read-Only:** Hardware automatically sets pending bits

**Interrupt Sources:**
- **MSIP (bit 3)**: CLINT software interrupt (write to MSIP register)
- **MTIP (bit 7)**: CLINT timer interrupt (mtime >= mtimecmp)
- **MEIP (bit 11)**: PLIC external interrupt (device interrupt routed through PLIC)

### mtvec (Trap Vector Base Address)

```systemverilog
logic [XLEN-1:0] mtvec;
```

**Format:**
```
31                    2 1   0
+----------------------+-----+
| BASE[31:2]           | MODE|
+----------------------+-----+
```

**Modes:**
- **MODE = 00 (Direct)**: All exceptions/interrupts jump to BASE
- **MODE = 01 (Vectored)**: Exceptions → BASE, Interrupts → BASE + 4×cause

**Example:**
```assembly
# Set trap vector to 0x80000000 (Direct mode)
lui x1, 0x80000
csrrw x0, mtvec, x1     # mtvec = 0x80000000
```

**Trap Target Calculation:**
```
PC = (MODE == 0) ? BASE : (is_interrupt ? BASE + 4×cause : BASE)
```

### mepc (Exception Program Counter)

```systemverilog
logic [XLEN-1:0] mepc;
```

**Saved PC on Trap Entry:**
- **Exception:** Address of faulting instruction
- **Interrupt:** Address of interrupted instruction (or next instruction)

**MRET Return Address:**
```systemverilog
pc_target_o = mepc;  // Jump back to exception PC
```

**Alignment:** Must be 2-byte aligned (LSB ignored for RV32C)

### mcause (Exception Cause)

```systemverilog
logic [XLEN-1:0] mcause;
```

**Format:**
```
31 30                              0
+--+--------------------------------+
|I |      Exception Code            |
+--+--------------------------------+
```

- **Interrupt (bit 31)**: 1 = Interrupt, 0 = Exception
- **Exception Code (bits 30:0)**: Cause identifier

**Exception Codes:**
| Code | Name | Description |
|------|------|-------------|
| 0 | Instruction address misaligned | PC not 2-byte aligned |
| 1 | Instruction access fault | Memory access error |
| 2 | Illegal instruction | Invalid opcode/funct |
| 3 | Breakpoint | EBREAK instruction |
| 4 | Load address misaligned | Load address not aligned |
| 5 | Load access fault | Load memory error |
| 6 | Store address misaligned | Store address not aligned |
| 7 | Store access fault | Store memory error |
| 8 | Environment call from U-mode | ECALL (user) |
| 11 | Environment call from M-mode | ECALL (machine) |

**Interrupt Codes (bit 31 = 1):**
| Code | Name | Description |
|------|------|-------------|
| 3 | Machine software interrupt | CLINT software interrupt |
| 7 | Machine timer interrupt | CLINT timer interrupt |
| 11 | Machine external interrupt | PLIC external interrupt |

### mtval (Trap Value)

```systemverilog
logic [XLEN-1:0] mtval_reg;
```

**Saved on Trap Entry:**
- **Illegal instruction**: Faulting instruction encoding
- **Address misaligned**: Faulting address
- **Access fault**: Faulting address
- **Breakpoint**: PC of EBREAK instruction
- **Other exceptions**: 0

### mscratch (Scratch Register)

```systemverilog
logic [XLEN-1:0] mscratch;
```

**Usage:** Temporary storage for trap handlers (context save/restore)

**Example:**
```assembly
# Trap handler entry
csrrw x31, mscratch, x31  # Swap x31 ↔ mscratch
# Now x31 points to trap handler stack
```

### mcycle / mcycleh (Cycle Counter)

```systemverilog
logic [XLEN-1:0] mcycle;
logic [XLEN-1:0] mcycleh;
```

**64-bit Counter (RV32):**
```
{mcycleh, mcycle}  // 64-bit cycle count
```

**Increment:**
```systemverilog
{mcycleh, mcycle} <= {mcycleh, mcycle} + 64'd1;  // Every active cycle
```

**Stall Handling:** Increments even during stalls (real-time cycle count)

### minstret / minstreth (Instruction Counter)

```systemverilog
logic [XLEN-1:0] minstret;
logic [XLEN-1:0] minstreth;
```

**64-bit Counter (RV32):**
```
{minstreth, minstret}  // 64-bit instruction count
```

**Increment:**
```systemverilog
if (!trap_active_i) begin
  {minstreth, minstret} <= {minstreth, minstret} + 64'd1;  // Every retired instruction
end
```

**Not Incremented:**
- During traps
- During CSR writes to minstret/minstreth (Spike compatibility)

### tdata1 (Trigger Data 1)

```systemverilog
logic [XLEN-1:0] tdata1_reg;
```

**mcontrol Format (type = 2):**
```
31       28 27  20 19 18      12 11 10  7 6 5 4 3 2 1 0
+----------+------+---+---------+--+-----+-+-+-+-+-+-+-+
| type (2) | dmode| 0 | maskmax | 0| hit |m|0|s|u|x|w|r|
+----------+------+---+---------+--+-----+-+-+-+-+-+-+-+
```

**Fields:**
- **type (bits 31:28)**: 2 = mcontrol (address/data match)
- **dmode (bit 27)**: 0 = M-mode writable, 1 = Debug mode only
- **maskmax (bits 20:16)**: Not used (0)
- **hit (bit 20)**: Trigger fired (sticky)
- **m (bit 6)**: M-mode match enable
- **s (bit 4)**: S-mode match enable (not used)
- **u (bit 3)**: U-mode match enable (not used)
- **x (bit 2)**: Execute match (not implemented)
- **w (bit 1)**: Store match
- **r (bit 0)**: Load match

**Default Value:**
```systemverilog
tdata1_reg <= 32'h20000044;  // type=2, m=1, w=1, r=1
```

### tdata2 (Trigger Data 2)

```systemverilog
logic [XLEN-1:0] tdata2_reg;
```

**Usage:** Breakpoint address for mcontrol type

**Example:**
```c
// Set hardware breakpoint on address 0x80001000
write_csr(tdata2, 0x80001000);  // Breakpoint address
write_csr(tdata1, 0x20000043);  // mcontrol, M-mode, LOAD match
```

### tcontrol (Trigger Control)

```systemverilog
logic [XLEN-1:0] tcontrol_reg;
```

**Format:**
```
31       8 7    4 3    0
+---------+------+-----+
| (rsv=0) | MPTE | MTE |
+---------+------+-----+
```

**Fields:**
- **MTE (bit 3)**: M-mode Trigger Enable (1 = enable triggers in M-mode)
- **MPTE (bit 7)**: Previous MTE (saved on trap entry)

**Trap Entry:**
```systemverilog
tcontrol_reg[7] <= tcontrol_reg[3];  // mpte = mte (save)
```

**MRET:**
```systemverilog
tcontrol_reg[3] <= tcontrol_reg[7];  // mte = mpte (restore)
```

## Trap Handling Flow

### Trap Entry (Exception/Interrupt)

```systemverilog
if (trap_active_i || de_trap_active_i) begin
  mepc <= trap_mepc_i;            // Save exception PC
  mcause <= trap_cause_i;         // Save cause
  mtval_reg <= trap_tval_i;       // Save trap value
  mstatus.mpie <= mstatus.mie;    // Save interrupt enable
  mstatus.mie <= 1'b0;            // Disable interrupts
  mstatus.mpp <= 2'b11;           // Save privilege mode (M-mode)
  
  // Trigger control: save MTE to MPTE
  tcontrol_reg[7] <= tcontrol_reg[3];
end
```

**Trap Target:**
```
PC = mtvec  // Jump to trap handler
```

### MRET (Trap Return)

```systemverilog
if (instr_type_i == mret) begin
  mstatus.mie <= mstatus.mpie;    // Restore interrupt enable
  mstatus.mpie <= 1'b1;           // Set MPIE to 1 (convention)
  mstatus.mpp <= 2'b11;           // Remain in M-mode
  
  // Trigger control: restore MTE from MPTE
  tcontrol_reg[3] <= tcontrol_reg[7];
end
```

**Return Target:**
```
PC = mepc  // Jump back to exception PC
```

## Interrupt Priority

**Hardware Priority (highest to lowest):**
1. Machine External Interrupt (MEIP, bit 11)
2. Machine Timer Interrupt (MTIP, bit 7)
3. Machine Software Interrupt (MSIP, bit 3)

**Priority Logic (handled in trap controller):**
```systemverilog
if (mstatus.MIE) begin
  if (mip[11] && mie[11]) take_interrupt(11);  // MEIP
  else if (mip[7] && mie[7]) take_interrupt(7);   // MTIP
  else if (mip[3] && mie[3]) take_interrupt(3);   // MSIP
end
```

## CSR Access Control

### Read-Only CSRs

- Machine info: mvendorid, marchid, mimpid, mhartid, mconfigptr
- Interrupt pending: mip (hardware-driven)
- Optional stubs: scounteren, mcountinhibit, tselect, tdata3

**Write Ignored:** Writes to read-only CSRs are silently ignored

### WARL (Write-Any-Read-Legal)

**misa:**
- Only C extension bit is writable
- Other bits return fixed values

**mstatus:**
- MPP always reads as 2'b11 (M-mode only)
- Writes to reserved bits ignored

### Write-Through Bypass

**Trigger Registers:**
```systemverilog
tdata1_bypass = (wr_en_i && csr_idx_i == TDATA1) ? csr_wdata_i : tdata1_reg;
```

**Rationale:** Hardware breakpoint detection needs immediate visibility of written values (same-cycle usage)

## Performance Counters

### mcycle / mcycleh

**Increment Condition:**
```systemverilog
if (!(stall_i inside {IMISS_STALL, DMISS_STALL, ALU_STALL, FENCEI_STALL} && !trap_active_i)) begin
  {mcycleh, mcycle} <= {mcycleh, mcycle} + 64'd1;
end
```

**Incremented:**
- Every active cycle (no stall)
- During trap handling

**Not Incremented:**
- During cache miss stalls
- During ALU multi-cycle operation stalls

### minstret / minstreth

**Increment Condition:**
```systemverilog
if (!trap_active_i && !(wr_en_i && (csr_idx_i == MINSTRET || csr_idx_i == MINSTRETH))) begin
  {minstreth, minstret} <= {minstreth, minstret} + 64'd1;
end
```

**Incremented:**
- Every retired instruction

**Not Incremented:**
- During trap entry
- During CSR writes to minstret/minstreth (Spike timing compatibility)

## Debug Trigger Example

### Hardware Breakpoint on Load Address

```c
// Set breakpoint on load from address 0x80001234
void set_load_breakpoint(uint32_t addr) {
  write_csr(tdata2, addr);           // Breakpoint address
  write_csr(tdata1, 0x20000041);     // type=2, m=1, r=1 (LOAD match)
  write_csr(tcontrol, 0x00000008);   // MTE=1 (enable in M-mode)
}

// Execution
lw x1, 0(x2)  // If x2 + 0 == 0x80001234 → Breakpoint exception
```

### Hardware Breakpoint on Store Address

```c
void set_store_breakpoint(uint32_t addr) {
  write_csr(tdata2, addr);           // Breakpoint address
  write_csr(tdata1, 0x20000042);     // type=2, m=1, w=1 (STORE match)
  write_csr(tcontrol, 0x00000008);   // MTE=1
}
```

## Verification

### Test Cases

1. **CSR Read/Write:**
```assembly
csrrw x1, mstatus, x2   # Atomic read-write
csrrs x3, mie, x4       # Read-set bits
csrrc x5, mip, x6       # Read-clear bits (should fail, mip is RO)
```

2. **Trap Entry:**
```assembly
ecall                   # Should save PC, cause, disable interrupts
# Check: mepc, mcause, mstatus.MIE=0, mstatus.MPIE=old_MIE
```

3. **MRET:**
```assembly
mret                    # Should restore PC, interrupt enable
# Check: PC=mepc, mstatus.MIE=old_MPIE, mstatus.MPIE=1
```

4. **Performance Counters:**
```c
uint64_t start = read_cycle();
// ... code ...
uint64_t end = read_cycle();
uint64_t elapsed = end - start;
```

### Assertions

```systemverilog
// MIE only writable bits 3, 7, 11
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (wr_en_i && csr_idx_i == MIE_ADDR) |=> 
  ((mie & ~MIE_RW_MASK) == 0));

// mstatus.MPP always reads as 2'b11
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (rd_en_i && csr_idx_i == MSTATUS) |-> 
  (csr_rdata_o[12:11] == 2'b11));

// mip is read-only
assert property (@(posedge clk_i) disable iff (!rst_ni)
  (wr_en_i && csr_idx_i == MIP) |=> 
  $stable(mip));
```

## İlgili Modüller

1. **execution.sv**: CSR read/write interface
2. **alu.sv**: CSR operation logic (CSRRW/CSRRS/CSRRC)
3. **trap_controller.sv**: Trap detection and interrupt prioritization

## Referanslar

1. RISC-V Privileged ISA Specification v1.12 - Chapter 3 (Machine-Level ISA)
2. RISC-V Debug Specification v0.13.2 - Chapter 5 (Trigger Module)
3. "RISC-V External Debug Support" - RISC-V Foundation

---

**Son Güncelleme:** 5 Aralık 2025  
**Yazar:** Kerim TURAK  
**Lisans:** MIT License
