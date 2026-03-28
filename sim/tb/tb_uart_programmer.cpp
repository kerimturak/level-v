// Verify uart_send_data.py / ram_programmer path: payload bin → wrapper_ram words match .mem golden.
//
// Build (from repo root):
//   verilator +incdir+rtl/include -Wall -Wno-fatal -Wno-WIDTHTRUNC \
//     -cc --exe --build -j 0 \
//     --top-module tb_uart_programmer \
//     -Mdir build/obj_uart_programmer_verify \
//     rtl/pkg/level_param.sv rtl/wrapper/simpleuart.v rtl/wrapper/ram_programmer.sv \
//     rtl/wrapper/wrapper_ram.sv sim/tb/tb_uart_programmer.sv \
//     sim/tb/tb_uart_programmer.cpp
//
// Run:
//   python3 script/python/fpga/uart_send_data.py --mem build/tests/.../tiny.mem --dump-payload build/tests/uart_verify/payload.bin
//   build/obj_uart_programmer_verify/Vtb_uart_programmer \
//     +PAYLOAD=build/tests/uart_verify/payload.bin +GOLDEN=build/tests/.../tiny.mem

#include "Vtb_uart_programmer.h"
#include "verilated.h"

#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>
#include <vector>

static vluint64_t sim_time = 0;
double sc_time_stamp() { return sim_time; }

static const char* plusarg(int argc, char** argv, const char* key) {
    size_t n = std::strlen(key);
    for (int i = 1; i < argc; ++i) {
        if (std::strncmp(argv[i], key, n) == 0 && argv[i][n] != '\0') return argv[i] + n;
    }
    return nullptr;
}

static void clock_cycle(Vtb_uart_programmer* top) {
    top->clk_i = 0;
    top->eval();
    sim_time++;
    top->clk_i = 1;
    top->eval();
    sim_time++;
}

static void uart_send_byte(Vtb_uart_programmer* top, uint8_t b, unsigned bit_cycles) {
    auto hold = [&](int lv, unsigned bits) {
        top->ram_prog_rx_i = lv;
        for (unsigned i = 0; i < bits * bit_cycles; ++i) clock_cycle(top);
    };
    hold(0, 1);
    for (int i = 0; i < 8; ++i) hold((b >> i) & 1, 1);
    hold(1, 1);
    top->ram_prog_rx_i = 1;
    for (unsigned i = 0; i < bit_cycles * 4; ++i) clock_cycle(top);
}

static void stream_payload(Vtb_uart_programmer* top, const char* path, unsigned cpu_hz, unsigned baud,
                           unsigned bit_cycles_override) {
    std::ifstream in(path, std::ios::binary);
    if (!in) {
        std::cerr << "FATAL: cannot open +PAYLOAD file: " << path << "\n";
        std::exit(2);
    }
    std::vector<uint8_t> data((std::istreambuf_iterator<char>(in)), std::istreambuf_iterator<char>());
    unsigned div = (cpu_hz + baud / 2) / baud;
    if (div < 1) div = 1;
    // Default (div+1): simpleuart counts recv_divcnt > cfg_divider (217) → 218 clocks/bit at 25 MHz / 115200.
    unsigned bit_cycles = bit_cycles_override ? bit_cycles_override : (div + 1);
    std::cout << "[uart_verify] payload " << path << "  bytes=" << data.size() << "  cfg_div=" << div
              << "  bit_clks=" << bit_cycles << "\n";
    top->ram_prog_rx_i = 1;
    for (unsigned i = 0; i < bit_cycles * 8; ++i) clock_cycle(top);
    for (uint8_t byte : data) uart_send_byte(top, byte, bit_cycles);
    top->ram_prog_rx_i = 1;
}

static std::vector<uint32_t> load_mem_hex(const char* path) {
    std::ifstream f(path);
    if (!f) {
        std::cerr << "FATAL: cannot open +GOLDEN file: " << path << "\n";
        std::exit(2);
    }
    std::vector<uint32_t> words;
    std::string line;
    while (std::getline(f, line)) {
        while (!line.empty() && (line[0] == ' ' || line[0] == '\t')) line.erase(0, 1);
        if (line.empty() || line[0] == '/' || line[0] == '#') continue;
        if (line[0] == '@') continue;
        line = line.substr(0, line.find_first_of(" \t"));
        if (line.empty()) continue;
        uint32_t w = static_cast<uint32_t>(std::strtoul(line.c_str(), nullptr, 16));
        words.push_back(w);
    }
    return words;
}

static uint32_t wide_sel32(const VlWide<4>& w, unsigned lane) {
    return static_cast<uint32_t>(w.at(lane));
}

static void wide_zero(VlWide<4>& w) {
    for (size_t i = 0; i < w.size(); ++i) w.at(i) = 0;
}

static void ram_write_word(Vtb_uart_programmer* top, unsigned word_idx, uint32_t v) {
    unsigned lane = word_idx & 3u;
    for (size_t w = 0; w < 4; ++w) top->wdata_i.at(w) = v;
    top->addr_i = word_idx;
    top->rd_en_i = 0;
    top->wstrb_i = static_cast<uint16_t>(0xfu << (lane * 4));
    clock_cycle(top);
    top->wstrb_i = 0;
    clock_cycle(top);
}

static uint32_t ram_read_word(Vtb_uart_programmer* top, unsigned word_idx) {
    top->addr_i = word_idx;
    wide_zero(top->wdata_i);
    top->wstrb_i = 0;
    top->rd_en_i = 1;
    clock_cycle(top);
    top->rd_en_i = 0;
    clock_cycle(top);
    // VlWide packs [31:0] in word 0 of the verilog vector into m_storage[0]; Verilator order
    // matches addr_i[1:0] (LSW of 128b line = index 0).
    unsigned lane = word_idx & 3u;
    return wide_sel32(top->rdata_o, lane);
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    bool skip_payload = false;
    for (int i = 1; i < argc; ++i) {
        if (std::strcmp(argv[i], "+SKIP_PAYLOAD") == 0) skip_payload = true;
    }
    const char* payload = plusarg(argc, argv, "+PAYLOAD=");
    const char* golden_path = plusarg(argc, argv, "+GOLDEN=");
    if (!skip_payload && (!payload || !golden_path)) {
        std::cerr << "Usage: Vtb_uart_programmer +PAYLOAD=prog.bin +GOLDEN=test.mem [+SKIP_PAYLOAD] ...\n";
        return 1;
    }
    unsigned cpu_hz = 25000000u;
    unsigned baud = 115200;
    if (const char* s = plusarg(argc, argv, "+CPU_HZ=")) cpu_hz = static_cast<unsigned>(std::strtoul(s, nullptr, 10));
    if (const char* s = plusarg(argc, argv, "+BAUD=")) baud = static_cast<unsigned>(std::strtoul(s, nullptr, 10));
    unsigned bit_cycles_ov = 0;
    if (const char* s = plusarg(argc, argv, "+BIT_CYCLES="))
        bit_cycles_ov = static_cast<unsigned>(std::strtoul(s, nullptr, 10));

    std::vector<uint32_t> golden;
    if (!skip_payload) {
        golden = load_mem_hex(golden_path);
        if (golden.empty()) {
            std::cerr << "FATAL: golden is empty\n";
            return 2;
        }
        if (golden.size() > 1024u) {
            std::cerr << "FATAL: golden has " << golden.size() << " words; tb UART_programmer RAM_DEPTH=1024\n";
            return 2;
        }
    }

    Vtb_uart_programmer* top = new Vtb_uart_programmer;

    top->clk_i = 0;
    top->rst_ni = 0;
    top->ram_prog_rx_i = 1;
    top->addr_i = 0;
    wide_zero(top->wdata_i);
    top->wstrb_i = 0;
    top->rd_en_i = 0;
    for (int i = 0; i < 10; ++i) clock_cycle(top);
    top->rst_ni = 1;

    bool ram_selftest = false;
    for (int i = 1; i < argc; ++i) {
        if (std::strcmp(argv[i], "+RAM_RW_SELFTEST") == 0) ram_selftest = true;
    }
    if (ram_selftest) {
        ram_write_word(top, 100, 0xCAFEBABEu);
        uint32_t t = ram_read_word(top, 100);
        if (t != 0xCAFEBABEu) {
            std::cerr << "RAM RW selftest fail: got 0x" << std::hex << t << std::dec << "\n";
            delete top;
            return 4;
        }
        std::cout << "[uart_verify] RAM R/W selftest ok\n";
    }

    if (skip_payload) {
        delete top;
        return 0;
    }

    stream_payload(top, payload, cpu_hz, baud, bit_cycles_ov);

    /* Programmer idle; allow FSM to return to idle after ST_FINISH */
    int post_idle = 5000;
    if (const char* s = plusarg(argc, argv, "+POST_IDLE_CYCLES="))
        post_idle = static_cast<int>(std::strtoul(s, nullptr, 10));
    for (int i = 0; i < post_idle; ++i) clock_cycle(top);

    bool ok = true;
    for (size_t i = 0; i < golden.size(); ++i) {
        uint32_t got = ram_read_word(top, static_cast<unsigned>(i));
        if (got != golden[i]) {
            std::cerr << "MISMATCH word[" << i << "] golden=0x" << std::hex << golden[i] << " got=0x" << got << std::dec << "\n";
            ok = false;
            if (i > 8) break;
        }
    }

    delete top;

    if (!ok) {
        std::cerr << "[uart_verify] FAIL\n";
        return 3;
    }
    std::cout << "[uart_verify] PASS  " << golden.size() << " words\n";
    return 0;
}
