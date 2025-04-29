#!/usr/bin/env bash

# Colors for pretty output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Detect Python command
if command -v python3 &> /dev/null; then
    PYTHON_CMD=${PYTHON_CMD:-"python3"}
elif command -v python &> /dev/null; then
    PYTHON_CMD=${PYTHON_CMD:-"python"}
else
    echo -e "${RED}Neither python3 nor python found in PATH${NC}"
    exit 1
fi

# Configuration
TEST_DIR="efmc/tests"
COVERAGE_DIR="coverage_report"
export PYTHONDONTWRITEBYTECODE=1

# Parse command line arguments
VERBOSE=0
COVERAGE=0
RUN_SLOW=0
PARALLEL=0
SPECIFIC_TEST=""

print_usage() {
    echo -e "${BLUE}Usage: $0 [options]${NC}"
    echo "Options:"
    echo "  -h, --help        Show this help message"
    echo "  -v, --verbose     Show verbose output"
    echo "  -c, --coverage    Run with coverage report"
    echo "  -s, --slow        Include slow tests"
    echo "  -p, --parallel    Run tests in parallel"
    echo "  -t, --test TEST   Run specific test file or directory"
}

while [[ "$#" -gt 0 ]]; do
    case $1 in
        -h|--help) print_usage; exit 0 ;;
        -v|--verbose) VERBOSE=1 ;;
        -c|--coverage) COVERAGE=1 ;;
        -s|--slow) RUN_SLOW=1 ;;
        -p|--parallel) PARALLEL=1 ;;
        -t|--test) SPECIFIC_TEST="$2"; shift ;;
        *) echo "Unknown parameter: $1"; print_usage; exit 1 ;;
    esac
    shift
done

# Build pytest arguments as an array
PYTEST_ARGS=(-x)  # Exit on first failure

# Add verbosity
if [ "$VERBOSE" -eq 1 ]; then
    PYTEST_ARGS+=(-vv)
else
    PYTEST_ARGS+=(-v)
fi

# Handle slow tests
if [ "$RUN_SLOW" -eq 0 ]; then
    PYTEST_ARGS+=(-m "not slow")
fi

# Add parallel execution
if [ "$PARALLEL" -eq 1 ]; then
    PYTEST_ARGS+=(-n auto)
fi

# Add coverage
if [ "$COVERAGE" -eq 1 ]; then
    PYTEST_ARGS+=(--cov=efmc --cov-report=html:$COVERAGE_DIR --cov-report=xml:coverage.xml)
fi

# Set test target
TEST_TARGET="${SPECIFIC_TEST:-$TEST_DIR}"

echo -e "${YELLOW}Running tests with configuration:${NC}"
echo -e "  Python command: ${BLUE}$PYTHON_CMD${NC}"
echo -e "  Test target:    ${BLUE}$TEST_TARGET${NC}"
echo -e "  Pytest args:    ${BLUE}${PYTEST_ARGS[@]}${NC}"
echo "----------------------------------------"

# Run pre-test checks
echo -e "${YELLOW}Running pre-test checks...${NC}"
if ! command -v pytest &> /dev/null; then
    echo -e "${RED}pytest not found. Please install it with: pip install pytest${NC}"
    exit 1
fi

if [ "$COVERAGE" -eq 1 ]; then
    # Check if pytest-cov is installed by trying to import it
    if ! $PYTHON_CMD -c "import pytest_cov" &> /dev/null; then
        echo -e "${RED}pytest-cov not found. Please install it with: pip install pytest-cov${NC}"
        exit 1
    fi
fi

# Clean up previous coverage reports
if [ "$COVERAGE" -eq 1 ]; then
    rm -rf "$COVERAGE_DIR"
fi

# Run the tests
echo -e "${YELLOW}Running tests...${NC}"
set +e  # Don't exit on error
$PYTHON_CMD -m pytest "${PYTEST_ARGS[@]}" "$TEST_TARGET"
TEST_RESULT=$?
set -e  # Exit on error

# Post-test actions
if [ "$COVERAGE" -eq 1 ] && [ "$TEST_RESULT" -eq 0 ]; then
    echo -e "${GREEN}Coverage report generated in: $COVERAGE_DIR${NC}"
    echo -e "${BLUE}Open $COVERAGE_DIR/index.html in your browser to view the report${NC}"
fi

# Exit with test result
if [ "$TEST_RESULT" -eq 0 ]; then
    echo -e "${GREEN}All tests passed successfully!${NC}"
else
    echo -e "${RED}Tests failed with exit code $TEST_RESULT${NC}"
fi

exit $TEST_RESULT