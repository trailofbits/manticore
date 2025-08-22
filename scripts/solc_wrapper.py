#!/usr/bin/env python3
"""
Solidity compiler wrapper for Docker containers.

This wrapper provides compatibility between solc-select and solcjs (npm-installed solc)
by translating solc command-line arguments to solcjs format and handling options like --combined-json.
"""
import subprocess
import sys
import os
import json
import re
import tempfile


def parse_combined_json_options(options_str):
    """Parse the --combined-json options string."""
    # Standard combined-json options that solcjs supports
    supported_options = {
        'abi', 'ast', 'bin', 'bin-runtime', 'srcmap', 'srcmap-runtime',
        'userdoc', 'devdoc', 'metadata'
    }
    
    requested = set(options_str.split(','))
    return requested.intersection(supported_options)


def run_solcjs_with_combined_json(sol_file, options):
    """Run solcjs and create combined JSON output similar to solc."""
    output = {}
    contracts = {}
    
    # Convert to absolute path to avoid issues with working directory changes
    sol_file_abs = os.path.abspath(sol_file)
    
    # Use temporary directory for solcjs output
    with tempfile.TemporaryDirectory() as tmpdir:
        cmd = ['node', '/usr/bin/solcjs', sol_file_abs, '--output-dir', tmpdir]
        
        # Add output options
        if 'abi' in options:
            cmd.append('--abi')
        if 'bin' in options:
            cmd.append('--bin')
        
        # Run solcjs
        result = subprocess.run(cmd, capture_output=True, text=True)
        
        if result.returncode != 0:
            print(result.stderr, file=sys.stderr)
            return result.returncode
        
        # Process output files
        for filename in os.listdir(tmpdir):
            if filename.endswith('.abi'):
                contract_name = filename.replace('.abi', '').split('_')[-1]
                with open(os.path.join(tmpdir, filename)) as f:
                    if contract_name not in contracts:
                        contracts[contract_name] = {}
                    contracts[contract_name]['abi'] = json.load(f)
            
            elif filename.endswith('.bin'):
                contract_name = filename.replace('.bin', '').split('_')[-1]
                with open(os.path.join(tmpdir, filename)) as f:
                    if contract_name not in contracts:
                        contracts[contract_name] = {}
                    contracts[contract_name]['bin'] = f.read().strip()
    
    # Create combined JSON output
    output['contracts'] = {}
    for contract_name, contract_data in contracts.items():
        full_name = f"{sol_file}:{contract_name}"
        output['contracts'][full_name] = contract_data
    
    # Print combined JSON
    print(json.dumps(output))
    return 0


def main():
    """Main wrapper function that translates solc args to solcjs."""
    args = sys.argv[1:]
    
    # Handle --version separately
    if len(args) == 1 and args[0] == '--version':
        try:
            result = subprocess.run(['node', '/usr/bin/solcjs', '--version'], capture_output=True, text=True)
            if result.returncode == 0:
                print(result.stdout.strip())
                sys.exit(0)
            else:
                print("solcjs: command not found", file=sys.stderr)
                sys.exit(1)
        except FileNotFoundError:
            print("solcjs: command not found", file=sys.stderr)
            sys.exit(1)
    
    # Parse arguments for --combined-json
    combined_json_options = None
    sol_file = None
    i = 0
    
    while i < len(args):
        if args[i] == '--combined-json' and i + 1 < len(args):
            combined_json_options = args[i + 1]
            i += 2
        elif args[i].endswith('.sol'):
            sol_file = args[i]
            i += 1
        else:
            i += 1
    
    # Handle --combined-json case
    if combined_json_options and sol_file:
        options = parse_combined_json_options(combined_json_options)
        return run_solcjs_with_combined_json(sol_file, options)
    
    # For other cases, try to pass through to solcjs
    try:
        # Filter out incompatible arguments
        filtered_args = []
        skip_next = False
        
        for i, arg in enumerate(args):
            if skip_next:
                skip_next = False
                continue
                
            if arg == '--combined-json':
                skip_next = True
                continue
            elif arg.startswith('--allow-paths'):
                continue  # solcjs doesn't support this
            else:
                filtered_args.append(arg)
        
        result = subprocess.run(['node', '/usr/bin/solcjs'] + filtered_args, 
                              capture_output=False, check=False)
        sys.exit(result.returncode)
        
    except FileNotFoundError:
        print("Error: solcjs not found", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()