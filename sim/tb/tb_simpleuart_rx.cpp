// Drive ser_rx with UART-framed bytes; compare decoded bytes to file contents.
#include "Vtb_simpleuart_rx.h"
#include "verilated.h"
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <iterator>
#include <vector>

static vluint64_t t = 0;
double sc_time_stamp() { return t; }

static void clk(Vtb_simpleuart_rx* top) {
    top->clk_i = 0;
    top->eval();
    t++;
    top->clk_i = 1;
    top->eval();
    t++;
}

static void uart_byte(Vtb_simpleuart_rx* top, uint8_t b, unsigned bitclks) {
    auto hold = [&](int v, unsigned n) {
        top->ser_rx_i = v;
        for (unsigned i = 0; i < n * bitclks; ++i) clk(top);
    };
    hold(0, 1);
    for (int i = 0; i < 8; ++i) hold((b >> i) & 1, 1);
    hold(1, 1);
    top->ser_rx_i = 1;
    for (unsigned i = 0; i < 4 * bitclks; ++i) clk(top);
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    if (argc < 3) {
        std::cerr << "usage: Vtb_simpleuart_rx <binfile> <bit_clocks_per_bit>\n";
        return 1;
    }
    std::ifstream in(argv[1], std::ios::binary);
    std::vector<uint8_t> send(std::istreambuf_iterator<char>(in), {});
    unsigned bitclks = static_cast<unsigned>(std::strtoul(argv[2], nullptr, 10));

    Vtb_simpleuart_rx* top = new Vtb_simpleuart_rx;
    top->clk_i = 0;
    top->rst_ni = 0;
    top->ser_rx_i = 1;
    top->reg_dat_re_i = 0;
    for (int i = 0; i < 5; ++i) clk(top);
    top->rst_ni = 1;
    for (unsigned i = 0; i < 8 * bitclks; ++i) clk(top);

    std::vector<uint8_t> got;
    for (uint8_t b : send) {
        uart_byte(top, b, bitclks);
        int spin = 0;
        while (top->reg_dat_do_o == 0xffffffffu && spin < 100000) {
            clk(top);
            spin++;
        }
        if (top->reg_dat_do_o == 0xffffffffu) {
            std::cerr << "timeout after byte 0x" << std::hex << (unsigned)b << std::dec << "\n";
            return 2;
        }
        uint8_t r = static_cast<uint8_t>(top->reg_dat_do_o & 0xff);
        top->reg_dat_re_i = 1;
        clk(top);
        top->reg_dat_re_i = 0;
        clk(top);
        got.push_back(r);
    }

    delete top;
    if (got != send) {
        for (size_t i = 0; i < send.size() && i < got.size(); ++i) {
            if (got[i] != send[i]) {
                std::cerr << "MISMATCH i=" << i << " exp=0x" << std::hex << (unsigned)send[i] << " got=0x"
                          << (unsigned)got[i] << std::dec << "\n";
                return 3;
            }
        }
        return 3;
    }
    std::cout << "simpleuart_rx OK bitclks=" << bitclks << " bytes=" << got.size() << "\n";
    return 0;
}
