#!/bin/bash
# 
# Ceres RISC-V Documentation Manifest
# Generated: 2025-12-01
# Purpose: Quick reference for all documentation files
#

cat << 'EOF'

╔═══════════════════════════════════════════════════════════════════════════╗
║                   CERES RISC-V DOCUMENTATION MANIFEST                    ║
║                                                                           ║
║  Comprehensive documentation for Ceres 32-bit RISC-V processor core      ║
║  Implementing RV32IMC with parametric exception priority system          ║
╚═══════════════════════════════════════════════════════════════════════════╝

📚 DOCUMENTATION STRUCTURE
═════════════════════════════════════════════════════════════════════════════

🔴 ENTRY POINTS (Başlama Noktaları)
───────────────────────────────────────────────────────────────────────────
  1. docs/INDEX.md                    ⭐ START HERE - Merkezi harita
  2. docs/GETTING_STARTED.md          ⭐ Yeni başlayanlar için
  3. docs/DOCUMENTATION_SUMMARY.md    ⭐ Bu belgeler özeti (senaryolar)

📖 MAIN DOCUMENTATION (Ana Belgeler)
───────────────────────────────────────────────────────────────────────────
  ✓ docs/architecture.md
    ├─ 5-stage pipeline mimarisi
    ├─ Exception Priority sistem
    ├─ CSR yönetimi
    ├─ Cache tasarımı
    ├─ Debug & Trace
    └─ 16 detaylı bölüm, 45-60 min okuma

  ✓ docs/DESIGN_CUSTOMIZATION.md
    ├─ Parametrik konfigürasyon
    ├─ ISA uzantıları (RV32M, RV32C)
    ├─ Bellek & Cache parametreleri
    ├─ Exception Priority custom tanımları
    ├─ Pratik örnekler (Minimal, Performance, FPGA)
    └─ 10 öğretici bölüm, 60 min okuma

  ✓ docs/PARAMETRIC_EXCEPTION_PRIORITY.md
    ├─ Exception Priority derinlemesine
    ├─ Configuration şablonları
    ├─ Testing workflow
    ├─ Debugging stratejileri
    └─ 8 detaylı bölüm

  ✓ docs/IMPLEMENTATION_SUMMARY.md
    ├─ Priority Level enumerasyonu
    ├─ Configuration parametreleri
    ├─ Priority Check fonksiyonu
    └─ Code locations & timing

🔧 TECHNICAL GUIDES (Teknik Kılavuzlar)
───────────────────────────────────────────────────────────────────────────
  ✓ docs/riscv-test.md
    └─ RISC-V ISA test framework kurulum

  ✓ docs/COREMARK_BUILD.md
    └─ CoreMark benchmark setup

  ✓ docs/CUSTOM_UART_TEST_GUIDE.md
    └─ Custom test yazma rehberi

  ✓ docs/TOOLS.md
    ├─ Verilator kurulum
    ├─ RISC-V Toolchain
    ├─ Simulation Tools
    └─ Debugging Tools

🐛 ADVANCED TOPICS (İleri Konular)
───────────────────────────────────────────────────────────────────────────
  ✓ docs/fence_i_implementation.md
    └─ FENCE.I (instruction cache flush)

  ✓ docs/ras.md
    └─ Return Address Stack & Branch Prediction

  ✓ docs/rad_guide.md
    └─ RAM Access Debugging

  ✓ docs/bug_report_002.md
    └─ Known issues & workarounds

📋 REFERENCE (Referans)
───────────────────────────────────────────────────────────────────────────
  ✓ docs/defines.md
    ├─ ISA tanımları
    ├─ CSR adresleri
    └─ Exception kodları

🗂️  ADDITIONAL FILES
───────────────────────────────────────────────────────────────────────────
  • docs/README.md                     (Brief intro)
  • docs/doc.md                        (Legacy: Python Pipeline)
  • docs/doc2.md                       (Legacy: Statistics)

═════════════════════════════════════════════════════════════════════════════

📊 DOCUMENTATION STATISTICS
═════════════════════════════════════════════════════════════════════════════

Total Documents:           18 files
New Documents (Dec 1):     4 files ⭐
Updated Documents:         2 files
Total Content:             ~35,000 words
Total Read Time:           ~4 hours

NEW DOCUMENTS CREATED:
  ⭐ architecture.md              (32 KB) - Complete architecture reference
  ⭐ DESIGN_CUSTOMIZATION.md      (16 KB) - Parametric configuration guide
  ⭐ GETTING_STARTED.md           (7.5 KB) - Quick start for new users
  ⭐ INDEX.md                     (5.7 KB) - Central documentation map
  ⭐ DOCUMENTATION_SUMMARY.md     (14 KB) - This file

UPDATED DOCUMENTS:
  ✓ README.md                    - Added documentation references

═════════════════════════════════════════════════════════════════════════════

🎯 QUICK REFERENCE BY SCENARIO
═════════════════════════════════════════════════════════════════════════════

"I want to get started quickly (1 hour)"
  1. GETTING_STARTED.md (30 min)
  2. INDEX.md (10 min)
  3. architecture.md - Sections 1-2 (20 min)

"I want to write tests (2 hours)"
  1. GETTING_STARTED.md
  2. CUSTOM_UART_TEST_GUIDE.md
  3. riscv-test.md
  4. architecture.md - Sections 2-3

"I want to understand the full design (3-4 hours)"
  1. INDEX.md (10 min)
  2. architecture.md - All sections (90 min)
  3. PARAMETRIC_EXCEPTION_PRIORITY.md (40 min)
  4. IMPLEMENTATION_SUMMARY.md (20 min)
  5. Review RTL code (rtl/core/)

"I want to customize the design (2-3 hours)"
  1. architecture.md (60 min)
  2. DESIGN_CUSTOMIZATION.md (90 min)
  3. Make modifications & test

"I want to optimize performance (2 hours)"
  1. architecture.md - Sections 11-12
  2. ras.md
  3. COREMARK_BUILD.md
  4. DESIGN_CUSTOMIZATION.md - Example 2

"I need to debug issues (1-2 hours)"
  1. GETTING_STARTED.md - Troubleshooting
  2. bug_report_002.md
  3. architecture.md - Section 14
  4. rad_guide.md

═════════════════════════════════════════════════════════════════════════════

📍 DIRECTORY STRUCTURE
═════════════════════════════════════════════════════════════════════════════

docs/
├── INDEX.md                              (Main entry point)
├── GETTING_STARTED.md                    (New user guide)
├── DOCUMENTATION_SUMMARY.md              (This summary)
├── architecture.md                       (Full technical reference)
├── DESIGN_CUSTOMIZATION.md               (Parametric config guide)
│
├── PARAMETRIC_EXCEPTION_PRIORITY.md      (Exception handling)
├── IMPLEMENTATION_SUMMARY.md             (Implementation details)
│
├── CUSTOM_UART_TEST_GUIDE.md             (Test writing)
├── riscv-test.md                         (ISA tests)
├── COREMARK_BUILD.md                     (Benchmark)
│
├── TOOLS.md                              (Tool setup)
├── defines.md                            (ISA definitions)
├── fence_i_implementation.md             (FENCE.I design)
├── ras.md                                (Branch prediction)
├── rad_guide.md                          (Debug guide)
├── bug_report_002.md                     (Known issues)
│
├── README.md                             (Intro)
├── doc.md                                (Legacy)
├── doc2.md                               (Legacy)
│
└── (subdirectories)
    ├── test/                             (Test automation docs)
    ├── coremark/                         (CoreMark details)
    ├── makefiles/                        (Build system)
    ├── verilator/                        (Verilator specific)
    ├── OoO/                              (Out-of-order notes)
    ├── fetch/                            (Fetch stage notes)
    ├── backup_changes/                   (Change history)

═════════════════════════════════════════════════════════════════════════════

🔗 INTERNAL REFERENCES
═════════════════════════════════════════════════════════════════════════════

architecture.md references:
  → Exception Priority: See PARAMETRIC_EXCEPTION_PRIORITY.md
  → Implementation: See IMPLEMENTATION_SUMMARY.md
  → Custom tests: See CUSTOM_UART_TEST_GUIDE.md

DESIGN_CUSTOMIZATION.md references:
  → Architecture: See architecture.md
  → Exception Priority: See PARAMETRIC_EXCEPTION_PRIORITY.md
  → Testing: See riscv-test.md

INDEX.md references:
  → Getting started: See GETTING_STARTED.md
  → All topics: See this DOCUMENTATION_SUMMARY.md

═════════════════════════════════════════════════════════════════════════════

🚀 QUICK COMMANDS
═════════════════════════════════════════════════════════════════════════════

View documentation overview:
  $ cat docs/INDEX.md

Get started quickly:
  $ cat docs/GETTING_STARTED.md

Find specific topic:
  $ grep -r "Your Topic" docs/

Read complete architecture:
  $ cat docs/architecture.md

Learn parametric customization:
  $ cat docs/DESIGN_CUSTOMIZATION.md

View this summary:
  $ cat docs/DOCUMENTATION_SUMMARY.md

═════════════════════════════════════════════════════════════════════════════

✅ DOCUMENTATION COMPLETENESS CHECKLIST
═════════════════════════════════════════════════════════════════════════════

Architecture & Design:
  [✓] Complete pipeline documentation
  [✓] Exception Priority detailed explanation
  [✓] CSR implementation details
  [✓] Cache architecture
  [✓] Debug & Trace systems
  [✓] Performance metrics

Customization & Configuration:
  [✓] Parametric system explanation
  [✓] ISA extensions (RV32M, RV32C)
  [✓] Memory configuration
  [✓] Cache parameters
  [✓] Build system options
  [✓] Practical examples (3 scenarios)

Testing & Validation:
  [✓] Quick start guide
  [✓] Test automation explanation
  [✓] Custom test writing guide
  [✓] ISA test framework
  [✓] Benchmark setup
  [✓] Coverage analysis

Tools & Infrastructure:
  [✓] Tool installation guide
  [✓] Verilator configuration
  [✓] RISC-V Toolchain setup
  [✓] Debug tools (GDB, Spike)

Advanced Topics:
  [✓] FENCE.I implementation
  [✓] Branch prediction (RAS)
  [✓] RAM debugging (RAD)
  [✓] Memory ordering

Support & Reference:
  [✓] Troubleshooting guide
  [✓] Known issues & workarounds
  [✓] ISA definitions
  [✓] Central documentation map

Navigation & Index:
  [✓] Documentation summary (this file)
  [✓] Entry points guide
  [✓] Scenario-based reading paths
  [✓] Cross-references

═════════════════════════════════════════════════════════════════════════════

📞 USAGE TIPS
═════════════════════════════════════════════════════════════════════════════

1. Start with INDEX.md if you don't know where to begin
2. Use GETTING_STARTED.md for first-time setup
3. Read architecture.md for design understanding
4. Use DESIGN_CUSTOMIZATION.md to modify the design
5. Follow DOCUMENTATION_SUMMARY.md (this file) for scenario-based learning
6. Cross-reference related topics using "See also" sections
7. Always check bug_report_002.md before opening a new issue
8. Use grep to search across all documentation

═════════════════════════════════════════════════════════════════════════════

📝 VERSION & UPDATES
═════════════════════════════════════════════════════════════════════════════

Documentation Version:  1.0
Last Updated:           2025-12-01
Status:                 ✅ Active & Current
Next Review:            2025-12-31

Changes in v1.0 (2025-12-01):
  • Added comprehensive architecture documentation
  • Created design customization guide
  • Created getting started guide
  • Created documentation index & summary
  • Updated main README.md with references

═════════════════════════════════════════════════════════════════════════════

For questions or contributions, see the main repository documentation.

EOF
