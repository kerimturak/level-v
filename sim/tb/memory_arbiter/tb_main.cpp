// Simple main file for Verilator testbench
#include "Vtb_memory_arbiter.h"
#include "verilated.h"
#include "verilated_fst_c.h"

// Verilator timing support
vluint64_t main_time = 0;
double sc_time_stamp() { return main_time; }

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);

    Vtb_memory_arbiter* tb = new Vtb_memory_arbiter;

    VerilatedFstC* tfp = new VerilatedFstC;
    tb->trace(tfp, 99);
    tfp->open("waveform.fst");

    const vluint64_t max_time = 10000000; // 10M ticks

    while (!Verilated::gotFinish() && main_time < max_time) {
        tb->eval();
        if (tfp) tfp->dump(main_time);
        main_time++;
    }

    tfp->close();
    delete tfp;
    delete tb;
    return 0;
}
