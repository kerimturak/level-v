#!/bin/bash
# Script to apply debug logging patches to CoreMark source files
# This script should be run from the coremark subrepo directory

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
COREMARK_DIR="$(pwd)"

echo "Applying debug patches to CoreMark sources..."
echo "Script dir: $SCRIPT_DIR"
echo "CoreMark dir: $COREMARK_DIR"

# Apply patches
echo "Applying core_main_debug.patch..."
patch -p1 < "$SCRIPT_DIR/core_main_debug.patch"

echo "Applying core_list_join_debug.patch..."
patch -p1 < "$SCRIPT_DIR/core_list_join_debug.patch"

echo "Applying core_matrix_debug.patch..."
patch -p1 < "$SCRIPT_DIR/core_matrix_debug.patch"

echo "Applying core_state_debug.patch..."
patch -p1 < "$SCRIPT_DIR/core_state_debug.patch"

echo "Debug patches applied successfully!"
