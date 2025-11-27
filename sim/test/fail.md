rv32mi-p-breakpoint
rv32mi-p-csr                // spike have different misa configuration and passing to user mod which we dont have
rv32mi-p-illegal            // 
rv32mi-p-ma_fetch
rv32mi-p-mcsr               // geçiyor sadece spike ve core misa farklı
rv32mi-p-pmpaddr            // çözülebilir
rv32mi-p-scall              // ECALL'ın mcause değerini yanlış hesaplıyorsun. yine machine mod dışı bir mode geöiyor spike
rv32mi-p-zicntr             // bu geçiyor spike sonsuz döngüye giriyor gibi



