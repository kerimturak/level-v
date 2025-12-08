#include <iostream>
#include <cstdint>
#include "Vpma_tb.h"
#include "verilated.h"

int main(int argc, char **argv) {
    Verilated::commandArgs(argc, argv);
    Vpma_tb* tb = new Vpma_tb;

    auto probe = [&](uint32_t addr){
        // Top-level port name is tb_addr_i
        tb->tb_addr_i = addr;
        tb->eval();
        std::cout << std::hex << "addr=0x" << addr
                  << " uncached=" << int(tb->tb_uncached_o)
                  << " memregion=" << int(tb->tb_memregion_o)
                  << " exec=" << int(tb->tb_grand_o)
                  << std::dec << std::endl;
    };

    std::cout << "PMA test - probing addresses" << std::endl;
    probe(0x80000000);
    probe(0x20000000);
    probe(0x30000000);
    probe(0x20100000);

    delete tb;
    return 0;
}
