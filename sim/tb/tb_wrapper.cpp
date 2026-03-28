#include "Vlevel_wrapper.h"
#include "verilated.h"

// Verilator passes -DVM_TRACE_FST=0 when FST is off; `defined(VM_TRACE_FST)` is still true,
// so use `#if VM_TRACE_FST` / `#if VM_TRACE` (undefined names are treated as 0).
#if VM_TRACE_FST
#include "verilated_fst_c.h"
#elif VM_TRACE
#include "verilated_vcd_c.h"
#endif

#if VM_COVERAGE
#include "verilated_cov.h"
#endif

#include <cstring>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>
#include <vector>
#include <cstdlib>

static vluint64_t main_time = 0;
double sc_time_stamp() { return main_time; }

// Verilator plusargs: +KEY=value  →  argv contains the full string
static const char* parse_plusarg(int argc, char** argv, const char* key) {
    const size_t n = std::strlen(key);
    for (int i = 1; i < argc; ++i) {
        if (std::strncmp(argv[i], key, n) == 0 && argv[i][n] != '\0')
            return argv[i] + n;
    }
    return nullptr;
}

static unsigned parse_u_plusarg(int argc, char** argv, const char* key, unsigned def_val) {
    const char* v = parse_plusarg(argc, argv, key);
    if (!v || !*v) return def_val;
    return static_cast<unsigned>(std::strtoul(v, nullptr, 10));
}

// One positive clock edge pair; trace sample on each half-cycle when enabled.
static void clock_cycle(Vlevel_wrapper* top, vluint64_t& mt, void* tracep) {
    top->clk_i = 0;
    top->eval();
#if VM_TRACE_FST
    if (tracep) static_cast<VerilatedFstC*>(tracep)->dump(mt++);
#elif VM_TRACE
    if (tracep) static_cast<VerilatedVcdC*>(tracep)->dump(mt++);
#else
    (void)tracep;
    mt++;
#endif
    top->clk_i = 1;
    top->eval();
#if VM_TRACE_FST
    if (tracep) static_cast<VerilatedFstC*>(tracep)->dump(mt++);
#elif VM_TRACE
    if (tracep) static_cast<VerilatedVcdC*>(tracep)->dump(mt++);
#else
    mt++;
#endif
}

// 8N1 @ cycles_per_bit (matches simpleuart DEFAULT_DIV = cpu_hz / baud)
// simpleuart bit period uses (cfg_divider+1) clock edges per bit (recv_divcnt > divider).
static void uart_send_byte_prog(Vlevel_wrapper* top, vluint64_t& mt, void* tracep, uint8_t b,
                                unsigned bit_cycles) {
    auto hold = [&](int level, unsigned nbits) {
        top->prog_rx_i = level;
        for (unsigned i = 0; i < nbits * bit_cycles; ++i) clock_cycle(top, mt, tracep);
    };
    hold(0, 1);  // start
    for (int i = 0; i < 8; ++i) hold((b >> i) & 1, 1);
    hold(1, 1);  // stop
    top->prog_rx_i = 1;
    for (unsigned i = 0; i < bit_cycles * 4; ++i) clock_cycle(top, mt, tracep);  // inter-byte idle
}

static void run_prog_uart_payload(Vlevel_wrapper* top, vluint64_t& mt, void* tracep,
                                  const char* path, unsigned cpu_hz, unsigned baud) {
    std::ifstream in(path, std::ios::binary);
    if (!in) {
        std::cerr << "[ERROR] +PROG_UART_PAYLOAD: cannot open: " << path << std::endl;
        std::exit(1);
    }
    std::vector<uint8_t> data((std::istreambuf_iterator<char>(in)), std::istreambuf_iterator<char>());
    unsigned div = (cpu_hz + baud / 2) / baud;
    if (div < 1) div = 1;
    unsigned bit_cycles = div + 1;
    std::cout << "[INFO] UART programmer stream: " << path << " (" << data.size() << " bytes), cfg_div=" << div
              << " bit_clks=" << bit_cycles << std::endl;
    top->prog_rx_i = 1;
    for (unsigned i = 0; i < bit_cycles * 8; ++i) clock_cycle(top, mt, tracep);  // idle line before magic
    for (uint8_t byte : data) uart_send_byte_prog(top, mt, tracep, byte, bit_cycles);
    top->prog_rx_i = 1;
    std::cout << "[INFO] UART programmer stream done; sim cycle ~" << (mt / 2) << std::endl;
}

int main(int argc, char** argv) {
    VerilatedContext* contextp = new VerilatedContext;
    contextp->commandArgs(argc, argv);

#if VM_TRACE_FST || VM_TRACE
    Verilated::traceEverOn(true);
#endif

    Vlevel_wrapper* top = new Vlevel_wrapper{contextp};

#if VM_TRACE_FST
    VerilatedFstC* tfp = new VerilatedFstC;
    top->trace(tfp, 99);
    const char* dump_file = "waveform.fst";
#elif VM_TRACE
    VerilatedVcdC* tfp = new VerilatedVcdC;
    top->trace(tfp, 99);
    const char* dump_file = "waveform.vcd";
#endif

#if VM_TRACE_FST || VM_TRACE
    for (int i = 1; i < argc; ++i) {
        if (std::strncmp(argv[i], "+DUMP_FILE=", 11) == 0) dump_file = argv[i] + 11;
    }
    tfp->open(dump_file);
    std::cout << "[TRACE] Waveform dump enabled: " << dump_file << std::endl;
#endif

    void* tracep = nullptr;
#if VM_TRACE_FST
    tracep = tfp;
#elif VM_TRACE
    tracep = tfp;
#endif

    top->clk_i = 0;
    top->rst_ni = 0;
    top->uart0_rx_i = 1;
    top->prog_rx_i = 1;

    for (int i = 0; i < 10; ++i) {
        clock_cycle(top, main_time, tracep);
    }

    top->rst_ni = 1;

    const char* payload_path = parse_plusarg(argc, argv, "+PROG_UART_PAYLOAD=");
    if (payload_path && *payload_path) {
        unsigned cpu_hz = parse_u_plusarg(argc, argv, "+PROG_CPU_CLK=", 25000000u);
        unsigned baud = parse_u_plusarg(argc, argv, "+PROG_BAUD=", 115200);
        run_prog_uart_payload(top, main_time, tracep, payload_path, cpu_hz, baud);
    }

    uint64_t MAX_CYCLES = (argc > 1) ? std::strtoull(argv[1], nullptr, 10) : 100000ULL;
    std::cout << "[INFO] Starting Verilator simulation (" << MAX_CYCLES << " cycles max)" << std::endl;

    uint64_t progress_interval = (MAX_CYCLES > 10000) ? (MAX_CYCLES / 10) : 1000;

    while (!contextp->gotFinish() && (main_time / 2) < MAX_CYCLES) {
        if (((main_time / 2) % progress_interval) == 0 && (main_time / 2) > 0) {
            std::cout << "[CYCLE] " << (main_time / 2) << "/" << MAX_CYCLES << std::endl;
        }

        clock_cycle(top, main_time, tracep);
    }

#if VM_TRACE_FST || VM_TRACE
    tfp->close();
    delete tfp;
#endif

    top->final();

#if VM_COVERAGE
    const char* coverage_file = "coverage.dat";
    for (int i = 1; i < argc; ++i) {
        if (std::strncmp(argv[i], "+COVERAGE_FILE=", 15) == 0) coverage_file = argv[i] + 15;
    }
    VerilatedCov::write(coverage_file);
    std::cout << "[COVERAGE] Data written to: " << coverage_file << std::endl;
#endif

    Verilated::flushCall();

    std::cout << "[INFO] Simulation finished after " << (main_time / 2) << " cycles." << std::endl;

    delete top;
    delete contextp;
    return 0;
}
