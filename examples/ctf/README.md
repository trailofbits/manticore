# Real World CTF Challenge Solutions

This directory contains Manticore-based solutions to real CTF (Capture The Flag) challenges and educational binary exploitation problems. These examples demonstrate practical applications of symbolic execution for solving security challenges.

## Overview

These examples showcase how Manticore can be used to:
- Automatically solve reverse engineering challenges
- Find valid inputs for complex validation logic
- Generate exploits from crashes
- Analyze both Linux binaries and Ethereum smart contracts

## Challenges Included

### Binary Challenges

#### 1. **ais3_crackme** - AIS3 Crackme Challenge
- Simple password cracking using symbolic execution
- Expected flag: `ais3{I_tak3_g00d_n0t3s}`

#### 2. **google2016_unbreakable** - Google CTF 2016
- Complex binary with multiple validation stages
- Demonstrates path exploration without manual RE
- Expected flag: `CTF{0The1Quick2Brown3Fox4Jumps5Over6The7Lazy8Fox9}`

#### 3. **hxp2018_angrme** - HXP CTF 2018
- PIE-enabled binary requiring ASLR handling
- Expected flag: `hxp{4nd_n0w_f0r_s0m3_r3al_ch4ll3ng3}`

#### 4. **internetwache15_re60** - Internetwache CTF 2015
- File format validation challenge
- Expected flag: `IW{FILE_CHeCKa}`

#### 5. **manticore_challenge** - Custom Manticore Challenge
- Demonstrates basic symbolic execution
- Expected flag: `=MANTICORE=`

#### 6. **pwnable_collision** - Pwnable.kr Collision
- Hash collision challenge
- Finds 20-byte input causing integer overflow

#### 7. **exploit_generation** - Automated Exploit Generation
- Converts crashes into working exploits
- Demonstrates hybrid concrete/symbolic execution

#### 8. **rpisec_mbe** - RPISEC MBE Labs
- Educational labs from Modern Binary Exploitation course
- Serial validation and switch case analysis

#### 9. **bugsbunny2017_rev150** - BugsBunny CTF 2017
- 20-digit password cracking via incremental search
- Hook-based injection and retry logic
- Expected solution: `42813724579039578812`

### Ethereum Challenges

#### 1. **polyswarm_challenge** - PolySwarm Smart Contract
- Ethereum contract reverse engineering
- Finds input to match specific hash: `b"dogecointothemoonlambosoondudes!"`

## Usage

Each challenge directory contains:
- The original binary/contract
- Python solution script using Manticore
- README with detailed explanation

To run any challenge:
```bash
cd [challenge_directory]
python [challenge_name].py
```

## Requirements

- Manticore symbolic execution framework
- Python 3.6+
- For binary challenges: Linux environment (or VM)
- For Ethereum challenges: solc compiler

## Notes

- Some challenges may require specific architecture (x86 vs x64)
- PIE/ASLR challenges may need address adjustments
- Execution time varies based on challenge complexity
- These are educational examples for learning symbolic execution

## Credits

Challenges sourced from various CTF competitions and educational materials:
- Google CTF
- HXP CTF
- Internetwache CTF
- AIS3 CTF
- BugsBunny CTF
- Pwnable.kr
- PolySwarm
- RPISEC MBE Course