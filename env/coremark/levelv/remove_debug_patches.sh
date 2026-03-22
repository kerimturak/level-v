#!/bin/bash
# Script to remove debug logging patches from CoreMark source files
# This script should be run from the coremark subrepo directory

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
COREMARK_DIR="$(pwd)"

echo "Removing debug patches from CoreMark sources..."
echo "Script dir: $SCRIPT_DIR"
echo "CoreMark dir: $COREMARK_DIR"

# Remove patches (reverse apply)
echo "Removing core_main_debug.patch..."
patch -R -p1 < "$SCRIPT_DIR/core_main_debug.patch"

echo "Removing core_list_join_debug.patch..."
patch -R -p1 < "$SCRIPT_DIR/core_list_join_debug.patch"

echo "Removing core_matrix_debug.patch..."
patch -R -p1 < "$SCRIPT_DIR/core_matrix_debug.patch"

echo "Removing core_state_debug.patch..."
patch -R -p1 < "$SCRIPT_DIR/core_state_debug.patch"

echo "Debug patches removed successfully!"
