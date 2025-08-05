# Quick Installation Guide

## Overview

This guide will help you install and run the refactored Bilinear Identity-Based Proxy Re-Encryption (IB-PRE) library.

## Prerequisites

- Python 3.8 or higher
- pip package manager

## Installation Steps

### 1. Install Dependencies

First, install the required cryptographic framework:

```bash
# For Ubuntu/Debian
sudo apt-get update
sudo apt-get install python3-dev libssl-dev libgmp-dev libpbc-dev

# Then install Python dependencies
pip install charm-crypto matplotlib networkx numpy pandas
```

### 2. Set Up the Library

```bash
# Navigate to the project directory
cd /workspace

# Install in development mode (recommended)
pip install -e bilinear_ibpre/

# Or set PYTHONPATH if you prefer not to install
export PYTHONPATH="/workspace:$PYTHONPATH"
```

### 3. Quick Test

Test the installation with a simple example:

```python
# test_installation.py
from bilinear_ibpre import CollusionResistantIBPRE

# Initialize and test basic functionality
ibpre = CollusionResistantIBPRE(security_parameter=80)
msk, params = ibpre.setup()

# Test encryption/decryption
alice_key = ibpre.key_generation("alice")
ciphertext = ibpre.encrypt("Hi", "alice")
decrypted = ibpre.decrypt(ciphertext, "alice")

print(f"✅ Success! Decrypted: {decrypted}")
```

## Running Examples

### Basic Usage Example
```bash
cd bilinear_ibpre/examples
python3 basic_usage.py
```

### Performance Testing
```bash
cd bilinear_ibpre/examples
python3 performance_example.py --quick
```

## Running Tests

```bash
cd bilinear_ibpre
python3 -m pytest tests/ -v
```

## Troubleshooting

### Common Issues

1. **Charm-crypto installation fails**: 
   - Make sure you have the required system dependencies
   - Try using conda: `conda install -c conda-forge pycrypto`

2. **Import errors**:
   - Ensure PYTHONPATH includes the project directory
   - Verify all dependencies are installed

3. **Performance issues**:
   - Start with low security parameters (80 bits) for testing
   - Use short messages (1-3 characters) for compatibility

### Getting Help

- Check the main README.md for comprehensive documentation
- Review example files for usage patterns
- Run tests to verify functionality

## What's New in the Refactored Version

✅ **Modular Architecture**: Clean separation into core, utils, diagrams, and examples
✅ **Visualization**: Connection diagrams and performance plots  
✅ **Performance Testing**: Comprehensive benchmarking tools
✅ **Type Safety**: Full type hints throughout
✅ **Better Documentation**: Extensive examples and API documentation
✅ **Testing**: Automated test suite
✅ **Easy Installation**: Setup.py and requirements.txt

## Next Steps

1. Run the basic example to familiarize yourself with the API
2. Explore the visualization capabilities with ConnectionDiagram
3. Benchmark performance on your hardware
4. Adapt the examples for your specific use case

Happy coding! 🎉