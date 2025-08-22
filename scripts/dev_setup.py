#!/usr/bin/env python3
"""
Developer setup script for Manticore on macOS/Linux
Helps configure the development environment with proper dependencies
"""

import sys
import os
import subprocess
import platform
import shutil


def print_header(msg):
    """Print a formatted header message"""
    print(f"\n{'=' * 60}")
    print(f"  {msg}")
    print(f"{'=' * 60}\n")


def run_command(cmd, check=True):
    """Run a shell command and return success status"""
    try:
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True, check=check)
        if result.returncode == 0:
            return True, result.stdout
        return False, result.stderr
    except subprocess.CalledProcessError as e:
        return False, str(e)


def check_python_version():
    """Check if Python version meets requirements"""
    if sys.version_info < (3, 9):
        print(f"❌ Python 3.9+ required, found {sys.version}")
        return False
    print(f"✅ Python {sys.version.split()[0]} meets requirements")
    return True


def check_solc():
    """Check Solidity compiler installation"""
    solc_path = shutil.which("solc")
    if not solc_path:
        print("⚠️  solc not found. You may want to install it for Ethereum contract analysis:")
        if platform.system() == "Darwin":
            print("    brew install solidity")
            print("    OR")
            print("    pip install solc-select && solc-select install 0.4.24")
        else:
            print("    sudo apt install solc")
            print("    OR")
            print("    pip install solc-select && solc-select install 0.4.24")
        return False
    
    success, output = run_command("solc --version", check=False)
    if success:
        version_line = [l for l in output.split('\n') if 'Version:' in l]
        if version_line:
            version = version_line[0].split(':')[1].split('+')[0].strip()
            print(f"✅ Found solc {version}")
            
            # Check version compatibility
            major, minor = map(int, version.split('.')[:2])
            if major == 0 and minor >= 8:
                print("   ⚠️  Note: Solc 0.8+ may have issues with older test contracts")
                print("   Consider using solc-select to manage multiple versions")
        return True
    return False


def check_z3():
    """Check Z3 solver installation"""
    z3_path = shutil.which("z3")
    if not z3_path:
        print("⚠️  z3 not found. Installing for better SMT solving:")
        if platform.system() == "Darwin":
            print("    brew install z3")
        else:
            print("    sudo apt install z3")
        return False
    
    print("✅ Found z3 solver")
    return True


def setup_venv():
    """Setup Python virtual environment"""
    print_header("Setting up Python virtual environment")
    
    if os.path.exists(".venv"):
        print("✅ Virtual environment already exists")
    else:
        success, _ = run_command(f"{sys.executable} -m venv .venv")
        if success:
            print("✅ Created virtual environment")
        else:
            print("❌ Failed to create virtual environment")
            return False
    
    # Detect venv activation command
    venv_python = ".venv/bin/python" if platform.system() != "Windows" else ".venv\\Scripts\\python"
    
    # Upgrade pip
    print("📦 Upgrading pip...")
    run_command(f"{venv_python} -m pip install --upgrade pip", check=False)
    
    # Install package
    print("📦 Installing Manticore in development mode...")
    success, output = run_command(f"{venv_python} -m pip install -e '.[dev-noks]'")
    if success:
        print("✅ Manticore installed successfully")
    else:
        print("❌ Failed to install Manticore")
        print(output)
        return False
    
    return True


def setup_solc_select(venv_python):
    """Setup solc-select for managing Solidity versions"""
    print_header("Setting up solc-select for Solidity version management")
    
    success, _ = run_command(f"{venv_python} -m pip install solc-select")
    if not success:
        print("❌ Failed to install solc-select")
        return False
    
    print("✅ solc-select installed")
    print("📦 Installing recommended Solidity versions...")
    
    versions = ["0.4.24", "0.5.11", "0.8.0"]
    for version in versions:
        print(f"   Installing solc {version}...")
        run_command(f"{venv_python} -m solc_select install {version}", check=False)
    
    # Set default version
    run_command(f"{venv_python} -m solc_select use 0.4.24", check=False)
    print("✅ Set default solc to 0.4.24 (best for tests)")
    
    return True


def print_next_steps():
    """Print next steps for the developer"""
    print_header("Setup Complete! Next Steps")
    
    if platform.system() != "Windows":
        print("1. Activate virtual environment:")
        print("   source .venv/bin/activate")
    else:
        print("1. Activate virtual environment:")
        print("   .venv\\Scripts\\activate")
    
    print("\n2. Run tests:")
    print("   pytest tests/                    # Run all tests")
    print("   pytest tests/ -m 'not slow'      # Skip slow tests")
    print("   pytest tests/ethereum/           # Run only Ethereum tests")
    
    print("\n3. Useful commands:")
    print("   solc-select list                 # List installed solc versions")
    print("   solc-select use 0.5.11           # Switch solc version")
    print("   pytest --markers                 # Show available test markers")
    
    print("\n4. For macOS users:")
    print("   - Native binary analysis has limited support")
    print("   - Consider using Docker/Linux VM for full functionality")
    print("   - WASM and Ethereum analysis work well on macOS")


def main():
    """Main setup function"""
    print_header("Manticore Developer Setup")
    
    system = platform.system()
    print(f"🖥️  Detected OS: {system}")
    
    if system == "Linux":
        print("✅ Linux is fully supported")
    elif system == "Darwin":
        print("⚠️  macOS has partial support (some native analysis features limited)")
    else:
        print("⚠️  Windows support is experimental")
    
    # Check prerequisites
    print_header("Checking Prerequisites")
    
    if not check_python_version():
        return 1
    
    check_solc()
    check_z3()
    
    # Setup environment
    if not setup_venv():
        return 1
    
    # Detect venv python
    venv_python = ".venv/bin/python" if platform.system() != "Windows" else ".venv\\Scripts\\python"
    
    # Setup solc-select if desired
    response = input("\n🔧 Setup solc-select for managing Solidity versions? (recommended) [Y/n]: ")
    if response.lower() != 'n':
        setup_solc_select(venv_python)
    
    print_next_steps()
    
    return 0


if __name__ == "__main__":
    sys.exit(main())