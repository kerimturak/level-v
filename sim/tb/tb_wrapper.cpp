#include "Vceres_wrapper.h"
#include "verilated.h"

#if defined(VM_TRACE_FST)
#include "verilated_fst_c.h"
#elif defined(VM_TRACE)
#include "verilated_vcd_c.h"
#endif

#if VM_COVERAGE
#include "verilated_cov.h"
#endif

#include <iostream>
#include <cstdlib>
#include <cstring>
#include <string>

static vluint64_t main_time = 0;
double sc_time_stamp() { return main_time; }

int main(int argc, char **argv) {
    // Create Verilator simulation context
    VerilatedContext* contextp = new VerilatedContext;
    contextp->commandArgs(argc, argv);

#if defined(VM_TRACE_FST) || defined(VM_TRACE)
    Verilated::traceEverOn(true);
#endif

    // Instantiate DUT
    Vceres_wrapper* top = new Vceres_wrapper{contextp};

#if defined(VM_TRACE_FST)
    VerilatedFstC* tfp = new VerilatedFstC;
    top->trace(tfp, 99);
    const char* dump_file = "waveform.fst";
#elif defined(VM_TRACE)
    VerilatedVcdC* tfp = new VerilatedVcdC;
    top->trace(tfp, 99);
    const char* dump_file = "waveform.vcd";
#endif

#if defined(VM_TRACE_FST) || defined(VM_TRACE)
    // Parse +DUMP_FILE= argument (optional)
    for (int i = 1; i < argc; ++i) {
        if (strncmp(argv[i], "+DUMP_FILE=", 11) == 0)
            dump_file = argv[i] + 11;
    }

    tfp->open(dump_file);
    std::cout << "[TRACE] Waveform dump enabled: " << dump_file << std::endl;
#endif

    // Initialize DUT signals
    top->clk_i     = 0;
    top->rst_ni    = 0;
    top->uart0_rx_i = 1;

    // --- Reset phase (10 cycles) ---
    for (int i = 0; i < 10; ++i) {
        top->clk_i = 0; top->eval();
#if defined(VM_TRACE_FST) || defined(VM_TRACE)
        tfp->dump(main_time++);
#endif
        top->clk_i = 1; top->eval();
#if defined(VM_TRACE_FST) || defined(VM_TRACE)
        tfp->dump(main_time++);
#endif
    }

    top->rst_ni = 1;

    // --- Simulation setup ---
    uint64_t MAX_CYCLES = (argc > 1) ? std::strtoull(argv[1], nullptr, 10) : 100000ULL;
    std::cout << "[INFO] Starting Verilator simulation (" << MAX_CYCLES << " cycles max)" << std::endl;
    
    // Calculate progress interval (every 10% of total cycles, minimum 1000)
    uint64_t progress_interval = (MAX_CYCLES > 10000) ? (MAX_CYCLES / 10) : 1000;

    // --- Main simulation loop ---
    while (!contextp->gotFinish() && (main_time / 2) < MAX_CYCLES) {
        // Print progress at regular intervals
        if (((main_time / 2) % progress_interval) == 0 && (main_time / 2) > 0) {
            std::cout << "[CYCLE] " << (main_time / 2) << "/" << MAX_CYCLES << std::endl;
        }
        
        top->clk_i = 0; top->eval();
#if defined(VM_TRACE_FST) || defined(VM_TRACE)
        tfp->dump(main_time++);
#endif
        top->clk_i = 1; top->eval();
#if defined(VM_TRACE_FST) || defined(VM_TRACE)
        tfp->dump(main_time++);
#endif
    }

#if defined(VM_TRACE_FST) || defined(VM_TRACE)
    tfp->close();
    delete tfp;
#endif

    top->final();

#if VM_COVERAGE
    // Write coverage data
    const char* coverage_file = "coverage.dat";
    for (int i = 1; i < argc; ++i) {
        if (strncmp(argv[i], "+COVERAGE_FILE=", 15) == 0)
            coverage_file = argv[i] + 15;
    }
    VerilatedCov::write(coverage_file);
    std::cout << "[COVERAGE] Data written to: " << coverage_file << std::endl;
#endif

    Verilated::flushCall();

    std::cout << "[INFO] Simulation finished after " << (main_time / 2)
              << " cycles." << std::endl;

    delete top;
    delete contextp;
    return 0;
}
