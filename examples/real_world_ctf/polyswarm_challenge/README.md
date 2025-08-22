# PolySwarm Smart Contract Challenge

## Challenge Overview

The PolySwarm challenge was a smart contract reverse engineering challenge where participants needed to find specific input bytes that would satisfy the contract's validation logic.

**Challenge Type**: Smart Contract Reverse Engineering  
**Platform**: Ethereum  
**Difficulty**: Medium  
**Original Author**: Raz0r  
**Writeup**: [Original Writeup](https://raz0r.name/writeups/polyswarm-smart-contract-hacking-challenge-writeup/)

## The Challenge

The challenge provided:
1. A deployed smart contract (`WinnerLog`) with obfuscated bytecode
2. The contract has a `logWinner` function that validates input data
3. The goal: Find the magic bytes that pass the validation

The contract contained the hint string "dogecointothemoonlambosoondudes!" embedded in the bytecode, but the validation logic was obfuscated.

## Solution Approach

### Using Symbolic Execution

Instead of manually reverse engineering the bytecode, we use Manticore's symbolic execution to:
1. Create a symbolic buffer for the input
2. Let Manticore explore all execution paths
3. Find inputs that lead to successful validation

### Files in This Directory

- `winnerlog.bin` - The original contract bytecode from the challenge
- `polyswarm_challenge.py` - Full solution attempting to deploy and solve the contract
- `polyswarm_simplified.py` - Simplified demonstration of the core technique

## Running the Examples

### Simplified Demo (Recommended)
```bash
python polyswarm_simplified.py
```

This demonstrates the core symbolic execution technique without the complexity of contract deployment.

### Full Solution (Advanced)
```bash
python polyswarm_challenge.py
```

Note: The full solution may have issues with contract deployment depending on your Manticore/solc setup.

## Key Learning Points

1. **Symbolic Buffers**: Creating symbolic input that Manticore can reason about
   ```python
   symbolic_data = m.make_symbolic_buffer(64)
   ```

2. **Constraint Solving**: Finding values that satisfy complex conditions
   ```python
   constraints.add((input_byte ^ key_byte) == target_byte)
   ```

3. **Path Exploration**: Manticore automatically explores different execution paths to find valid inputs

## The Magic String

The solution is: `dogecointothemoonlambosoondudes!`

This string was obfuscated in the contract's bytecode, but Manticore finds it through symbolic execution without needing to understand the obfuscation.

## Why This Matters

This challenge demonstrates:
- How symbolic execution can solve reverse engineering challenges
- The power of automated analysis vs manual reversing
- Real-world application of Manticore to security challenges

## Techniques Demonstrated

- Creating symbolic buffers
- Transaction simulation
- Constraint solving
- State exploration
- Extracting concrete values from symbolic execution

## Extension Ideas

If you want to practice more:
1. Modify the XOR key in the simplified example
2. Add additional constraints (e.g., must be alphanumeric)
3. Try multi-layer obfuscation
4. Create your own challenge contract and solve it

## References

- [Manticore EVM Documentation](https://github.com/trailofbits/manticore/wiki/Ethereum)
- [PolySwarm Platform](https://polyswarm.io/)
- [Symbolic Execution Explained](https://en.wikipedia.org/wiki/Symbolic_execution)