// Simple main file for Verilator testbench
#include "Vtb_dcache_selfcheck.h"
#include "verilated.h"
#include "verilated_fst_c.h"

// Verilator timing support
vluint64_t main_time = 0;
double sc_time_stamp() { return main_time; }

int main(int argc, char** argv) {
    // Initialize Verilator
    Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);

    // Create instance of testbench module
    Vtb_dcache_selfcheck* tb = new Vtb_dcache_selfcheck;

    // Create trace
    VerilatedFstC* tfp = new VerilatedFstC;
    tb->trace(tfp, 99);
    tfp->open("waveform.fst");

    // Run simulation with timing support (increased for extended tests)
    const vluint64_t max_time = 1000000000; // 1B time units (1000x longer)

    while (!Verilated::gotFinish() && main_time < max_time) {
        // Evaluate model
        tb->eval();

        // Dump waveform
        if (tfp) tfp->dump(main_time);

        // Advance time - let Verilator's timing scheduler handle delays
        main_time++;
    }

    printf("\n[INFO] Simulation ended at time %lu\n", main_time);

    if (Verilated::gotFinish()) {
        printf("[INFO] Simulation finished normally via $finish\n");
    } else {
        printf("[WARNING] Simulation ended due to timeout\n");
    }

    // Cleanup
    tfp->close();
    delete tfp;
    delete tb;

    return 0;
}
