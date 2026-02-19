#!/usr/bin/env python3
"""Extract SRAM macro instance names from an OpenLane ODB file.

Usage (inside OpenLane container):
    openroad -python dump_macro_names.py <odb_file>
"""

import sys
import odb

if len(sys.argv) < 2:
    print("Usage: dump_macro_names.py <odb_file>", file=sys.stderr)
    sys.exit(1)

odb_path = sys.argv[1]

reader = odb.dbDatabase.create()
odb.read_db(reader, odb_path)
block = reader.getChip().getBlock()

macros = []
for inst in block.getInsts():
    master = inst.getMaster()
    if master.isBlock():
        bb = inst.getBBox()
        macros.append((
            inst.getName(),
            master.getName(),
            bb.xMin() / 1000.0,
            bb.yMin() / 1000.0
        ))

macros.sort(key=lambda x: x[0])

print()
print("# ============================================================")
print("# SRAM Macro Instance Names (from ODB)")
print("# Format: instance_name  [master_cell]  @ (x, y)")
print("# ============================================================")
for name, master, x, y in macros:
    print(f"{name}  [{master}]  @ ({x:.1f}, {y:.1f})")

print()
print("# ============================================================")
print("# macro_placement.cfg format (copy and edit coordinates):")
print("# ============================================================")
for name, master, x, y in macros:
    print(f"{name}  {x:.0f}  {y:.0f}  N")
