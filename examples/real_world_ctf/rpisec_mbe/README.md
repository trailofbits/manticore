# RPISEC Modern Binary Exploitation Labs

These examples are from the RPISEC Modern Binary Exploitation course, demonstrating practical binary exploitation techniques using Manticore.

## Overview

The RPISEC MBE course is a university-level course on binary exploitation. These labs demonstrate how symbolic execution can solve reverse engineering challenges automatically.

## Labs Included

### Lab 1A - Serial Number Validation
- **Objective**: Find a valid serial number for a given username
- **Technique**: Hook-based analysis to extract calculated serial
- **Key Concept**: The binary calculates a serial from the username

### Lab 1B - Switch Case Analysis  
- **Objective**: Find the correct password from 21 switch cases
- **Technique**: Systematic case exploration with backtracking
- **Key Concept**: Brute-force through limited switch cases

## Usage

### Lab 1A:
```bash
python lab1A.py
```

Finds a valid serial number for the username "test123".

### Lab 1B:
```bash
python lab1B.py
```

Tests all switch cases to find the correct password.

## Educational Value

These labs demonstrate:
- **Performance optimization**: Skipping expensive libc calls
- **Hook-based analysis**: Intercepting and modifying execution
- **State manipulation**: Injecting data directly into memory
- **Systematic exploration**: Testing multiple paths efficiently

## Technical Details

- **Architecture**: Linux x86 (32-bit)
- **Course**: RPISEC Modern Binary Exploitation
- **Techniques**: Hooking, state injection, path exploration

## About RPISEC MBE

The Modern Binary Exploitation course by RPISEC (Rensselaer Polytechnic Institute Security Club) is a comprehensive introduction to binary exploitation techniques. These Manticore solutions show how symbolic execution can automate many reverse engineering tasks taught in the course.