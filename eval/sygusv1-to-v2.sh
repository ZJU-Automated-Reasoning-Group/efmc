# from CVC4
#!/bin/bash

set -euo pipefail

# Script configuration
VERSION="1.0.0"
SCRIPT_NAME=$(basename "$0")
LOG_DIR="logs"
TIMESTAMP=$(date '+%Y%m%d_%H%M%S')

# ANSI color codes
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Function to display usage information
show_usage() {
    cat << EOF
Usage: ${SCRIPT_NAME} [options] <path to cvc4> <path to sygus file> <path to output file> [<additional cvc4 options>*]

Converts SyGuS v1 files to SyGuS v2 format using CVC4.

Options:
    -h, --help          Show this help message
    -v, --verbose       Enable verbose output
    -f, --force         Overwrite output file if it exists
    --version           Show version information
    --no-color          Disable colored output
    --keep-options      Don't remove incremental and produce-models options

Arguments:
    <path to cvc4>          Path to CVC4 executable
    <path to sygus file>    Input SyGuS v1 file
    <path to output file>   Output file path for SyGuS v2
    [additional options]    Additional options passed to CVC4

Example:
    ${SCRIPT_NAME} /usr/bin/cvc4 input.sy output.sy --sygus-out=status
EOF
    exit 1
}

# Function to log messages
log() {
    local level=$1
    shift
    local message="$*"
    local log_file="${LOG_DIR}/${SCRIPT_NAME%.*}_${TIMESTAMP}.log"

    # Create log directory if it doesn't exist
    mkdir -p "${LOG_DIR}"

    # Format timestamp for log
    local timestamp=$(date '+%Y-%m-%d %H:%M:%S')

    # Write to log file
    echo "[${timestamp}] [${level}] ${message}" >> "${log_file}"

    # Print to stdout if verbose mode is enabled
    if [[ "${VERBOSE}" == "true" || "${level}" == "ERROR" ]]; then
        case "${level}" in
            "ERROR")   [[ "${NO_COLOR}" == "false" ]] && echo -e "${RED}[ERROR]${NC} ${message}" || echo "[ERROR] ${message}" ;;
            "WARNING") [[ "${NO_COLOR}" == "false" ]] && echo -e "${YELLOW}[WARNING]${NC} ${message}" || echo "[WARNING] ${message}" ;;
            "INFO")    [[ "${NO_COLOR}" == "false" ]] && echo -e "${GREEN}[INFO]${NC} ${message}" || echo "[INFO] ${message}" ;;
        esac
    fi
}

# Function to cleanup temporary files
cleanup() {
    if [[ -f "${TMP_FILE}" ]]; then
        rm -f "${TMP_FILE}"
    fi
}

# Initialize default values
VERBOSE=false
FORCE=false
NO_COLOR=false
KEEP_OPTIONS=false
TMP_FILE=""

# Parse command line options
while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help)
            show_usage
            ;;
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        -f|--force)
            FORCE=true
            shift
            ;;
        --version)
            echo "${SCRIPT_NAME} version ${VERSION}"
            exit 0
            ;;
        --no-color)
            NO_COLOR=true
            shift
            ;;
        --keep-options)
            KEEP_OPTIONS=true
            shift
            ;;
        *)
            break
            ;;
    esac
done

# Check required arguments
if [[ $# -lt 3 ]]; then
    log "ERROR" "Missing required arguments"
    show_usage
fi

CVC4_PATH="$1"
INPUT_FILE="$2"
OUTPUT_FILE="$3"
shift 3
ADDITIONAL_OPTS=("$@")

# Validate inputs
if [[ ! -x "${CVC4_PATH}" ]]; then
    log "ERROR" "CVC4 executable not found or not executable: ${CVC4_PATH}"
    exit 1
fi

if [[ ! -f "${INPUT_FILE}" ]]; then
    log "ERROR" "Input file not found: ${INPUT_FILE}"
    exit 1
fi

if [[ -f "${OUTPUT_FILE}" && "${FORCE}" != "true" ]]; then
    log "ERROR" "Output file already exists: ${OUTPUT_FILE}. Use -f to overwrite."
    exit 1
fi

# Create temporary file
TMP_FILE=$(mktemp)
trap cleanup EXIT

# Convert the file
log "INFO" "Converting ${INPUT_FILE} to SyGuS v2 format..."

output=$("${CVC4_PATH}" "${INPUT_FILE}" \
    --lang=sygus1 \
    --dump-to="${TMP_FILE}" \
    --output-lang=sygus2 \
    --dump=raw-benchmark \
    --preprocess-only \
    "${ADDITIONAL_OPTS[@]}" 2>&1)

exit_code=$?

if [[ ${exit_code} -eq 0 ]]; then
    if [[ "${KEEP_OPTIONS}" != "true" ]]; then
        # Remove incremental and produce-models options
        sed -i '/(set-option :incremental false)/d' "${TMP_FILE}"
        sed -i '/(set-option :produce-models "true")/d' "${TMP_FILE}"
    fi

    # Move temporary file to output location
    mv "${TMP_FILE}" "${OUTPUT_FILE}"
    log "INFO" "Conversion successful. Output written to: ${OUTPUT_FILE}"
else
    log "ERROR" "CVC4 failed with exit code ${exit_code}:"
    log "ERROR" "${output}"
    exit ${exit_code}
fi

# Verify output file exists and has content
if [[ ! -s "${OUTPUT_FILE}" ]]; then
    log "ERROR" "Output file is empty or does not exist: ${OUTPUT_FILE}"
    exit 1
fi

log "INFO" "Conversion completed successfully"