#!/bin/bash

# Setup the working environment of efmc without using dockerfile

# Exit on any error
set -e  # should we do this?

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VENV_DIR="${SCRIPT_DIR}/venv"

echo "Setting up EFMC environment..."

# Check if python3 is available, otherwise use python
PYTHON_CMD="python3"
if ! command -v python3 &> /dev/null; then
    PYTHON_CMD="python"
fi

# 1. Create virtual environment if it doesn't exist
if [ ! -d "${VENV_DIR}" ]; then
    echo "Creating virtual environment..."
    $PYTHON_CMD -m venv "${VENV_DIR}"
else
    echo "Virtual environment already exists."
fi

# 2. Activate virtual environment and install dependencies
echo "Activating virtual environment and installing dependencies..."
source "${VENV_DIR}/bin/activate"
pip install --upgrade pip
pip install -r "${SCRIPT_DIR}/requirements.txt"

# 3. Download solver binaries
echo "Downloading solver binaries..."
$PYTHON_CMD "${SCRIPT_DIR}/bin_solvers/download.py"

# 4. pysmt is installed in the venv, use pysmt-install to install BDD solver
# echo "Installing BDD solver..."
# pysmt-install --bdd

# 5. Run tests
echo "Running tests..."
if [ -f "${SCRIPT_DIR}/unit_tests.sh" ]; then
    bash "${SCRIPT_DIR}/unit_tests.sh"
else
    echo "Warning: unit_tests.sh not found"
fi

echo "Setup completed successfully!"