# Google CTF 2016: Unbreakable Enterprise Product Activation

## Challenge Overview

This was a reverse engineering challenge from Google CTF 2016. The challenge provided a binary that performs complex validation on user input to verify a product activation key.

**Challenge Name**: unbreakable-enterprise-product-activation  
**Category**: Reverse Engineering  
**Points**: 150  
**Platform**: Linux x86_64  

## The Challenge

The binary `unbreakable` asks for a product activation key and performs a series of complex checks to validate it. The goal is to find the correct activation key that passes all validation checks.

Traditional approach would require:
- Reverse engineering the binary in IDA/Ghidra
- Understanding the complex validation algorithm
- Manually working backwards to find valid input

## Manticore Solution

Instead of manual reverse engineering, we use symbolic execution to automatically find the valid input:

1. **Symbolic Input**: Create a symbolic buffer representing the unknown activation key
2. **Known Constraints**: Apply constraints for the known flag format (starts with "CTF{")
3. **Path Exploration**: Let Manticore explore all execution paths
4. **Hook Control**: Use hooks to:
   - Skip I/O operations and inject symbolic input directly
   - Abandon paths that lead to failure
   - Capture successful paths
5. **Solve**: Extract the concrete values that satisfy all constraints

## Files

- `unbreakable` - The original challenge binary (Linux x86_64 ELF)
- `google2016_unbreakable.py` - Manticore solution script
- `README.md` - This documentation

## Running the Solution

### Requirements
- Linux x86_64 system (or compatible environment)
- Manticore with native binary support
- Python 3.6+

### Execution
```bash
python google2016_unbreakable.py
```

### Expected Output
```
Google CTF 2016: Unbreakable Enterprise Product Activation
======================================================================

Loading binary: ./unbreakable

Setting up hooks...
  [*] Entry point reached - injecting symbolic input
  [-] Invalid input detected - abandoning path
  [-] Invalid input detected - abandoning path
  ...

🎉 Success state reached! Solving for flag...

✅ FLAG FOUND: CTF{0The1Quick2Brown3Fox4Jumped5Over6The7Lazy8Fox9}
```

## The Flag

The solution is: `CTF{0The1Quick2Brown3Fox4Jumped5Over6The7Lazy8Fox9}`

This seemingly random string actually passes all the complex validation checks in the binary.

## Key Addresses

Important addresses in the binary (found through static analysis):

- `0x400729` - Entry point where we hook to inject input
- `0x4005BD` - Start of validation checks (we jump here)
- `0x400850` - Failure function (paths here are abandoned)
- `0x400724` - Success function (flag is correct!)
- `0x6042C0` - Global buffer where input is stored
- `0x33` - Size of input buffer (51 bytes)

## Techniques Demonstrated

### 1. Symbolic Buffer Creation
```python
buffer = state.new_symbolic_buffer(0x43)
```
Creates a buffer where each byte is symbolic (unknown).

### 2. Constraint Application
```python
state.constrain(buffer[0] == ord("C"))
state.constrain(buffer[1] == ord("T"))
```
Reduces search space by applying known constraints.

### 3. Memory Manipulation
```python
state.cpu.write_bytes(INPUT_ADDR, buffer)
```
Writes symbolic data directly to memory.

### 4. Execution Control
```python
state.cpu.EIP = 0x4005BD  # Skip to validation
state.abandon()           # Stop exploring this path
```
Controls which code gets executed.

### 5. Concrete Value Extraction
```python
solution = state.solve_buffer(INPUT_ADDR, INPUT_SIZE)
```
Solves for concrete values that satisfy all constraints.

## Why This Works

The binary implements a complex validation algorithm that would be time-consuming to reverse engineer manually. However, from a symbolic execution perspective:

1. The validation is deterministic
2. There's a clear success/failure path
3. The input size is reasonable (51 bytes)
4. The constraints are solvable

Manticore automatically:
- Explores all possible execution paths
- Tracks constraints on the symbolic input
- Finds values that lead to the success path

## Platform Notes

⚠️ **Important**: This binary is compiled for Linux x86_64. It will not run natively on:
- macOS (different binary format)
- ARM processors (different architecture)
- 32-bit systems

For other platforms, you'll need:
- Docker/VM with Linux x86_64
- QEMU for architecture emulation
- Or recompile the challenge for your platform

## Learning Points

This challenge demonstrates that symbolic execution can be extremely powerful for:
- Bypassing complex validation logic
- Finding valid inputs without understanding the algorithm
- Automated reverse engineering
- CTF challenge solving

The same techniques can be applied to:
- License key validation
- Password checking routines
- Input validation bypasses
- Vulnerability research

## References

- [Original Challenge Writeup](https://github.com/ctfs/write-ups-2016/tree/master/google-ctf-2016/reverse/unbreakable-enterprise-product-activation-150)
- [Google CTF 2016](https://capturetheflag.withgoogle.com/)
- [Manticore Documentation](https://github.com/trailofbits/manticore)