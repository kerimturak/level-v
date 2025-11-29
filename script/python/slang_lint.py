#!/usr/bin/env python3
"""
Slang Linter Wrapper for CERES RISC-V
Uses pyslang to perform SystemVerilog linting
"""

import sys
import argparse
from pathlib import Path

try:
    import pyslang
except ImportError:
    print("Error: pyslang not installed. Install with: pip install pyslang")
    sys.exit(1)


def main():
    parser = argparse.ArgumentParser(description="Slang SystemVerilog Linter")
    parser.add_argument("files", nargs="*", help="SystemVerilog files to lint")
    parser.add_argument("-I", "--include", action="append", default=[], 
                        help="Include directories")
    parser.add_argument("--top", default=None, help="Top module name")
    parser.add_argument("-D", "--define", action="append", default=[],
                        help="Preprocessor defines")
    parser.add_argument("-v", "--verbose", action="store_true",
                        help="Verbose output")
    
    args = parser.parse_args()
    
    if not args.files:
        print("No files specified")
        sys.exit(1)
    
    # Create source manager and add include directories
    source_manager = pyslang.SourceManager()
    
    if args.include:
        for inc_dir in args.include:
            inc_path = Path(inc_dir)
            if inc_path.exists():
                source_manager.addUserDirectories(str(inc_path.absolute()))
    
    # Parse all files into syntax trees
    syntax_trees = []
    for file_path in args.files:
        path = Path(file_path)
        if not path.exists():
            if args.verbose:
                print(f"Warning: File not found: {file_path}")
            continue
        
        try:
            tree = pyslang.SyntaxTree.fromFile(str(path.absolute()), source_manager)
            syntax_trees.append(tree)
        except Exception as e:
            print(f"Error parsing {file_path}: {e}")
    
    if not syntax_trees:
        print("No valid files to process")
        sys.exit(1)
    
    # Create compilation and add all syntax trees
    compilation = pyslang.Compilation()
    for tree in syntax_trees:
        compilation.addSyntaxTree(tree)
    
    # Get all diagnostics
    diags = compilation.getAllDiagnostics()
    
    error_count = 0
    warning_count = 0
    
    # Create diagnostic engine for formatting
    diag_engine = pyslang.DiagnosticEngine(source_manager)
    
    for diag in diags:
        if diag.isError():
            error_count += 1
        else:
            warning_count += 1
        
        # Use the engine to format and report
        diag_engine.issue(diag)
    
    # Print formatted diagnostics  
    output = diag_engine.reportAll(source_manager, diags)
    if output:
        print(output)
    
    # Summary
    if args.verbose or error_count > 0 or warning_count > 0:
        print(f"\n{error_count} error(s), {warning_count} warning(s)")
    
    if error_count > 0:
        sys.exit(1)
    
    print("✓ Slang analysis complete")
    return 0


if __name__ == "__main__":
    sys.exit(main())
