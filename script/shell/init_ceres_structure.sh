#!/bin/bash

PROJECT_NAME="ceres-riscv"

echo "📁 Creating project directory: $PROJECT_NAME"
mkdir -p $PROJECT_NAME/{rtl/core,rtl/csr,rtl/alu,rtl/top}
mkdir -p $PROJECT_NAME/sim/{tb,test}
mkdir -p $PROJECT_NAME/sw/{asm,bin}
mkdir -p $PROJECT_NAME/doc
mkdir -p $PROJECT_NAME/verilator/cpp
mkdir -p $PROJECT_NAME/script/{sim,synth,lint,helper}

# Ana dosyalar
touch $PROJECT_NAME/Makefile
#touch $PROJECT_NAME/.gitignore
#touch $PROJECT_NAME/LICENSE
#touch $PROJECT_NAME/README.md

# RTL README'leri
echo "# RTL\nContains the synthesizable hardware modules." > $PROJECT_NAME/rtl/README.md
echo "# Core\nMain processor pipeline stages like fetch, decode, execute, etc." > $PROJECT_NAME/rtl/core/README.md
echo "# CSR\nControl and Status Register logic." > $PROJECT_NAME/rtl/csr/README.md
echo "# ALU\nArithmetic and logic unit responsible for integer operations." > $PROJECT_NAME/rtl/alu/README.md
echo "# Top\nTop-level wrapper module that instantiates all submodules." > $PROJECT_NAME/rtl/top/README.md

# Simülasyon klasörü README'leri
echo "# Simulation\nAll simulation-related files and testbenches." > $PROJECT_NAME/sim/README.md
echo "# Testbenches\nSystemVerilog/Verilog testbenches for simulation." > $PROJECT_NAME/sim/tb/README.md
echo "# Test Programs\nAssembly or binary programs used for functional tests." > $PROJECT_NAME/sim/test/README.md

# Yazılım klasörü README'leri
echo "# Software\nBare-metal programs for verifying functionality." > $PROJECT_NAME/sw/README.md
echo "# Assembly Programs\nLow-level RISC-V programs written in assembly." > $PROJECT_NAME/sw/asm/README.md
echo "# Compiled Outputs\nMachine-readable HEX/BIN files to load into memory." > $PROJECT_NAME/sw/bin/README.md

# Dokümantasyon README
echo "# Documentation\nArchitecture diagrams, ISA coverage, markdown specs." > $PROJECT_NAME/doc/README.md

# Verilator klasörü README
echo "# Verilator\nOptional C++ testbench support for Verilator-based simulation." > $PROJECT_NAME/verilator/README.md
echo "# C++ Files\nVerilator main, DPI modules, and memory model implementations." > $PROJECT_NAME/verilator/cpp/README.md

# Script klasörü README'leri
echo "# Scripts\nAll automation, tooling, and helper scripts for the project." > $PROJECT_NAME/script/README.md
echo "# Simulation Scripts\n. do files, .f files, and simulation helper tools." > $PROJECT_NAME/script/sim/README.md
echo "# Synthesis Scripts\nScripts for tools like Vivado, Yosys, or Quartus." > $PROJECT_NAME/script/synth/README.md
echo "# Lint Scripts\nLinting and static analysis tools such as Verilator or svlint." > $PROJECT_NAME/script/lint/README.md
echo "# Helper Scripts\nMakefile helpers, CI/CD scripts, formatting tools, etc." > $PROJECT_NAME/script/helper/README.md

echo "✅ Directory structure for '$PROJECT_NAME' created successfully!"
