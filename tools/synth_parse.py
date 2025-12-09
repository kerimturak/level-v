#!/usr/bin/env python3
"""
Simple parser for Vivado synthesis log -- extracts counts and critical items
"""
import sys
import re
from pathlib import Path

logfile = Path(sys.argv[1]) if len(sys.argv)>1 else Path('synthesis.log')
if not logfile.exists():
    print(f'Log file not found: {logfile}')
    sys.exit(2)

text = logfile.read_text()

# Extract counts
errors = len(re.findall(r"\bERRORS?\b|\bERROR:\b", text, re.I))
crit = len(re.findall(r"CRITICAL WARNING", text))
warnings = len(re.findall(r"WARNING", text))
infos = len(re.findall(r"INFO", text))

print(f'Parsed {logfile}\n  INFO count: {infos}, WARNING count: {warnings}, CRITICAL WARNING count: {crit}, ERRORS detected (regex): {errors}\n')

# Print critical warnings and their contexts
for m in re.finditer(r"CRITICAL WARNING:.*?$", text, re.M):
    start = m.start()
    context = text[start: start+400].splitlines()[:8]
    print('\n'.join(context))

# helper prints for common issues
print('\nTop 40 occurrences of unconnected-port warnings:')
for m in re.finditer(r"Port .*? either unconnected or has no load", text) :
    print(m.group())

# Any RAM inference problems
for m in re.finditer(r"Trying to implement RAM.*?$|Potential Runtime issue for RAM.*?$|dissolved into.*?registers bits", text, re.M):
    print('\nRAM issue:')
    a = m.group()
    print(a)

# Find timing loop excerpts
for m in re.finditer(r"found timing loop.*?$", text, re.M):
    print('\n'+m.group())

# end
