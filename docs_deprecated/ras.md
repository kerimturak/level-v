Tabii! Aşağıda RAS (Return Address Stack) modülünüzün işlevini ve nasıl çalıştığını açıklayan İngilizce teknik bir dokümantasyon yer alıyor. Bu dokümantasyon, başkalarının tasarımınızı anlaması ve kullanması için açıklayıcı bir formatta yazılmıştır.

---

# **RAS (Return Address Stack) Module Documentation**

## **Module Name**
`ras`

## **Project**
ceres RISC-V Processor

## **Author**
Kerim TURAK (kerimturak@hotmail.com)

---

## **Overview**

The Return Address Stack (RAS) module is a microarchitectural component designed to improve branch prediction accuracy during function calls and returns in a RISC-V pipeline. It keeps track of return addresses pushed during `call` instructions (e.g., `jal`) and predicts return targets during `ret` instructions (e.g., `jalr` with x1 or x5 as the target).

This module supports:
- Push (storing a return address)
- Pop (restoring a return address)
- Restore (flushing and restoring a specific PC)
- Both (pop + push in the same cycle)

---

## **Port Description**

| Port Name         | Direction | Width   | Description                                                                 |
|-------------------|----------|---------|-----------------------------------------------------------------------------|
| `clk_i`           | input    | 1 bit   | Clock signal.                                                              |
| `rst_ni`          | input    | 1 bit   | Active-low reset. Initializes internal stack to zero.                      |
| `spec_hit_i`      | input    | 1 bit   | Reserved for future use (e.g., speculative execution recovery).            |
| `restore_i`       | input    | 1 bit   | Triggers a stack restore operation with `restore_pc_i`.                    |
| `restore_pc_i`    | input    | 32 bit  | The PC value to restore into the top of the stack.                         |
| `req_valid_i`     | input    | 1 bit   | Indicates a valid instruction is being decoded.                            |
| `j_type_i`        | input    | 1 bit   | Indicates a J-type (direct jump) instruction.                              |
| `jr_type_i`       | input    | 1 bit   | Indicates a JR-type (jump register) instruction.                           |
| `rd_addr_i`       | input    | 5 bits  | Destination register address (rd).                                         |
| `r1_addr_i`       | input    | 5 bits  | Source register address (rs1).                                             |
| `return_addr_i`   | input    | 32 bit  | Return address to push into the stack (usually PC + 4).                    |
| `popped_addr_o`   | output   | 32 bit  | Return address popped from the stack (used for return prediction).        |
| `predict_valid_o` | output   | 1 bit   | High if the popped address is valid and should be used for prediction.    |

---

## **Internal Operation**

### **Stack Storage**

- Internal stack is a fixed-size array (`RAS_SIZE = 8`) of 32-bit addresses.
- New return addresses are inserted at index 0.
- Stack is shifted up or down on push/pop operations.

### **RAS Operation Types**
- **NONE:** No operation.
- **PUSH:** On valid `jal` or `jalr` where link register is written (x1 or x5).
- **POP:** On valid `jalr` where return address is expected from the stack.
- **BOTH:** When both rd and rs1 are link registers but point to different registers.

### **Link Detection**
The module uses a simplified convention:
- x1 (ra) and x5 (t0) are considered link registers.
- This allows compatibility with compilers that may use t0 for leaf-call optimization.

### **Control Logic (Combinational Block)**

- Determines the type of RAS operation (`ras_op`) based on instruction type and registers.
- Assigns the predicted return address (`popped_addr_o`).
- Sets `predict_valid_o` high only if a POP or BOTH operation is valid.

### **Update Logic (Sequential Block)**

- **On Reset:** Clears all entries in the RAS.
- **On Restore:** Inserts `restore_pc_i` at the top of the stack, shifts others down.
- **On Request (`req_valid_i`):**
  - **PUSH:** Inserts `return_addr_i` at top, shifts stack down.
  - **POP:** Removes top element, shifts remaining up.
  - **BOTH:** Replaces top element with new `return_addr_i`.

---

## **Design Assumptions and Notes**

- Stack overflow/underflow is not explicitly handled; designer must ensure usage within depth limits.
- `spec_hit_i` is reserved and not currently used.
- Designed for integration with 5-stage in-order RISC-V pipeline as part of the ceres project.
- Simple and efficient for small call depths; can be extended with pointer-based stack for deeper nesting.

---

## **Typical Use Case**

In a pipelined processor:

1. **Function Call (jal):**
   - `j_type_i = 1`, `rd_addr_i = x1`
   - `req_valid_i = 1`, `return_addr_i = PC+4`
   - Triggers a **PUSH** to save return address.

2. **Function Return (jalr):**
   - `jr_type_i = 1`, `r1_addr_i = x1`
   - `req_valid_i = 1`
   - Triggers a **POP**; output `popped_addr_o` provides predicted return address.

3. **Recursive Call (ra != rs1):**
   - Triggers a **BOTH**: pop the previous return and push a new one in the same cycle.

---

## **Conclusion**

This RAS module improves return address prediction for call/return control flow changes, which enhances the efficiency of a RISC-V pipeline. It’s designed to be simple yet extendable, and integrates seamlessly with a branch prediction unit or frontend instruction fetch stage.

---

Eğer istersen bu dokümantasyonu `.md` veya `.pdf` formatına da çevirebiliriz.