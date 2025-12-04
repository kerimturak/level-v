Aşağıdaki liste **riscv-tests** deposunun *isa/* klasörü altındaki alt dizinlerdir. Bunların her biri **RISC-V ISA (Instruction Set Architecture)** için farklı alt test gruplarını temsil eder. Yani bunlar ayrı “repo” değil, **test kategorileri / test setleri**dir.

Aşağıda hepsinin ne anlama geldiğini özetliyorum:

---

# 🧩 **Genel Yapı**

`riscv-tests/isa/` dizini altında RISC-V mimarisinin farklı **uzantıları (extensions)** ve **modları** için hazırlanmış resmi testler bulunur.

* **rv32** → 32-bit RISC-V (RV32) testleri
* **rv64** → 64-bit RISC-V (RV64) testleri
* Sonekler uzantıları belirtir:

  * **ui** → User Integer
  * **si** → Supervisor
  * **mi** → Machine mode
  * **ua/uc/ud/uf** → Atomic / Compressed / Double FP / Single FP
  * **um** → M extension (multiply/divide)
  * **uzxx** → Z* uzantıları (bit-manip, atomic subsets, vb.)
  * **hypervisor** → Hypervisor extension testleri

---

# 📁 **Dizinlerin Ayrıntılı Açıklaması**

## 📌 **Genel ISA klasörleri**

### **subrepo/riscv-tests/isa**

→ Ana klasör. Tüm ISA testleri burada.

### **hypervisor/**

→ RISC-V Hypervisor extension (H-extension) testleri.

### **macros/**

→ Testlerde kullanılan ortak makrolar.

---

# 🟦 **RV32 Test Grupları (32-bit)**

### **rv32ui**

User-level integer testleri (ADD, SUB, LW, SW, vb.)

### **rv32si**

Supervisor-level integer testleri.

### **rv32mi**

Machine-level testler (trap, exception, privilege testleri).

### **rv32ua**

A-extension: Atomic instructions (LR/SC, AMOs).

### **rv32uc**

C-extension: Compressed instructions.

### **rv32ud**

D-extension: Double-precision floating point.

### **rv32uf**

F-extension: Single-precision floating point.

### **rv32um**

M-extension: Multiply/divide instructions.

### Bit-manip veya yeni uzantılar:

* **rv32uzba** → Zba (Address generation bitmanip subset)
* **rv32uzbb** → Zbb (Basic bitmanip subset)
* **rv32uzbc** → Zbc (Carry-less multiply)
* **rv32uzbs** → Zbs (Shift operations)
* **rv32uzfh** → Zfh (Half-precision FP)

---

# 🟥 **RV64 Test Grupları (64-bit)**

RV32’nin 64-bit karşılıklarıdır:

### **rv64ui / rv64si / rv64mi**

→ 64-bit user/supervisor/machine testleri.

### **rv64ua / rv64uc / rv64ud / rv64uf**

→ Atomic, compressed, double/single FP.

### **rv64um**

→ M-extension 64-bit testleri.

### **rv64mzicbo**

→ Zicbo (cache block operations) testleri.

### **rv64ssvnapot**

→ NAPOT mappings (Svnapot extension) testleri.

### Bit-manip

* **rv64uzba**
* **rv64uzbb**
* **rv64uzbc**
* **rv64uzbs**

### Diğer:

* **rv64uzfh** → Half-precision FP
* **rv64uziccid** → ICCID extension (Instruction Cache Control / invalidate)

---

# 📌 **Özet**

Bu klasörlerin her biri:

✔ Bir **uzantıyı** (ör. M, A, C, F, D, Zb*, Zfh)
✔ Bir **modu** (user / supervisor / machine)
✔ Bir **bit genişliğini** (RV32 / RV64)

test etmek için oluşturulmuş **resmi RISC-V ISA doğrulama test kümeleridir**.

---

İstersen tek tek klasör içeriklerinin ne test ettiğini de açıklayabilirim.




rv32mi-p-breakpoint
rv32mi-p-csr          near to pass
rv32mi-p-illegal
rv32mi-p-ma_addr
rv32mi-p-ma_fetch     near to pass
rv32mi-p-mcsr         near to pass
rv32mi-p-pmpaddr      near to pass
rv32mi-p-scall        near to pass
rv32uc-p-rvc          passing   modelsim
rv32ui-p-fence_i
rv32ui-p-ma_data      passing
