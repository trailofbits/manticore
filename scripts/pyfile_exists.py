#!/usr/bin/env python3

import os
import sys

for f in sys.stdin.readlines():
    line = f.strip()
    if line.endswith('.py') and os.path.exists(line):
        print(line)
