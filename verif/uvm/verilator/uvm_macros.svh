// ============================================================================
// uvm_macros.svh SHIM'i (yalnizca Verilator akisinda kullanilir)
// ----------------------------------------------------------------------------
// Bu akista UVM, aracin kendi regresyonunda test edilen DUZLESTIRILMIS tek
// dosyadan gelir (uvm_pkg_all_v2020_3_1_nodpi.svh). O dosya hem uvm_pkg'i
// hem TUM UVM makrolarini zaten tanimlar ve makrolar ayni derleme kosusundaki
// sonraki dosyalarda gorunur kalir.
//
// Bu shim, kodumuzdaki `include "uvm_macros.svh" satirlarinin bu akista da
// cozulebilmesi icin vardir ve bilerek BOSTUR. Questa/VCS/Xcelium
// akislarinda +incdir sirasi geregi GERCEK uvm_macros.svh bulunur; bu dosya
// hic gorulmez.
//
// NOT: Yorumlarda satira "verilator" kelimesiyle baslamak, aracin metacomment
// (pragma) cozumleyicisini tetikler — bu dosyada bilerek kacinilmistir.
// ============================================================================
