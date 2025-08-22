# BugsBunny CTF 2017 - Rev 150

This challenge demonstrates an incremental password search technique using Manticore hooks to inject and test passwords systematically.

## Overview

The challenge binary expects a 20-digit numeric password. Through reverse engineering with IDA Pro, most digits can be deduced, leaving only a few positions to brute force.

## Solution Approach

1. **Initial Analysis**: Use IDA Pro to identify most password digits
2. **Starting Point**: Begin with password `42810720579039578812`
3. **Incremental Search**: Systematically increment specific digit positions
4. **Hook-based Testing**: Inject passwords and check results

## Key Techniques

### Password Injection Hook
```python
@m.hook(0x401be2)
def inject_password(state):
    # Inject 20-digit password at specific point
    state.cpu.write_bytes(state.cpu.RDI, formatted_pwd)
```

### Failure Handling
```python
@m.hook(0x401e5a)
def failed(state):
    # Increment password and retry
    context['password'] += 1000000000000
    state.cpu.RIP = 0x401be2  # Jump back
```

### Success Detection
```python
@m.hook(0x401e49)
def success(state):
    # Password found!
    print(f"Flag: BugsBunny{{{context['password']}}}")
```

## Usage

```bash
python bugsbunny2017_rev150.py
```

Or with custom binary:
```bash
python bugsbunny2017_rev150.py ./rev150 00000000000000000000
```

## Expected Output

```
[*] Injecting password: 42810720579039578812
[-] Incorrect password, trying next...
[*] Injecting password: 42811720579039578812
[-] Incorrect password, trying next...
[*] Injecting password: 42812720579039578812
[-] Incorrect password, trying next...
[*] Injecting password: 42813720579039578812
[+] Success!
[+] Password: 42813724579039578812
[+] Flag: BugsBunny{42813724579039578812}
```

## Technical Details

- **Architecture**: Linux x86_64
- **Password**: 20-digit numeric value
- **Solution**: `42813724579039578812`
- **Runtime**: ~9 minutes
- **Technique**: Hook-based incremental search

## Educational Value

This example demonstrates:
- Using hooks to inject data at specific program points
- Implementing retry logic by manipulating instruction pointer
- Incremental search strategies when partial information is known
- Combining static analysis (IDA Pro) with dynamic analysis (Manticore)

## Note

The challenge showcases how symbolic execution tools can be used for targeted searches when combined with reverse engineering insights. The incremental approach is more efficient than pure symbolic execution when most of the solution is already known.