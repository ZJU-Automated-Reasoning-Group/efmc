#!/bin/bash

# Configuration
SOLVERS=(
    "${Z3_ROOT}/bin/z3:fp.engine=spacer"
    "${ELDARICA_ROOT}/eld:)"  # Add more solvers in format "path:options"
)
BENCHMARK_DIR=$1
TIMEOUT=$2
NUM_PARALLEL=${3:-4}  # Default to 4 parallel jobs if not specified

# Create main output directory
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
BASE_OUTPUT_DIR="${OUTPUT_ROOT}/${TIMESTAMP}"
mkdir -p "${BASE_OUTPUT_DIR}"

# Log file for overall execution
MAIN_LOG="${BASE_OUTPUT_DIR}/execution.log"
echo "Execution started at $(date)" > "${MAIN_LOG}"
echo "Benchmark directory: ${BENCHMARK_DIR}" >> "${MAIN_LOG}"
echo "Timeout: ${TIMEOUT}" >> "${MAIN_LOG}"
echo "Number of parallel jobs: ${NUM_PARALLEL}" >> "${MAIN_LOG}"

# Function to run a single benchmark
run_benchmark() {
    local solver_path=$1
    local solver_options=$2
    local input_file=$3
    local output_dir=$4

    local filename=$(basename "${input_file}")
    local solver_name=$(basename "${solver_path}")
    local log_file="${output_dir}/${filename}"

    # Create a temporary file for detailed statistics
    local stats_file="${log_file}.stats"

    echo "Running ${solver_name} on ${filename}" >> "${MAIN_LOG}"

    # Run the solver and capture time/memory usage
    {
        /usr/bin/time -v timeout "${TIMEOUT}" "${solver_path}" ${solver_options} "${input_file}" \
            > "${log_file}.out" 2> "${log_file}.err"

        # Capture exit status
        echo "EXIT_STATUS=$?" > "${stats_file}"

        # Extract peak memory and time from time output
        grep "Maximum resident set size" "${log_file}.err" >> "${stats_file}"
        grep "User time" "${log_file}.err" >> "${stats_file}"
        grep "System time" "${log_file}.err" >> "${stats_file}"
        grep "Elapsed (wall clock) time" "${log_file}.err" >> "${stats_file}"
    } 2>> "${MAIN_LOG}"
}
export -f run_benchmark

# Process each solver
for solver_config in "${SOLVERS[@]}"; do
    # Split solver path and options
    IFS=: read -r solver_path solver_options <<< "${solver_config}"
    solver_name=$(basename "${solver_path}")

    # Create solver-specific output directory
    OUTPUT_DIR="${BASE_OUTPUT_DIR}/${solver_name}"
    mkdir -p "${OUTPUT_DIR}"

    echo "Processing solver: ${solver_name}" >> "${MAIN_LOG}"
    echo "Options: ${solver_options}" >> "${MAIN_LOG}"

    # Find all benchmark files and run them in parallel
    find "${BENCHMARK_DIR}" -name "*.smt2" | \
        parallel -j "${NUM_PARALLEL}" run_benchmark "${solver_path}" "${solver_options}" {} "${OUTPUT_DIR}"
done

# Generate summary report
SUMMARY_FILE="${BASE_OUTPUT_DIR}/summary.csv"
echo "Solver,Benchmark,Exit Status,Wall Time,User Time,System Time,Peak Memory" > "${SUMMARY_FILE}"

for solver_config in "${SOLVERS[@]}"; do
    solver_name=$(basename "${solver_config%%:*}")
    OUTPUT_DIR="${BASE_OUTPUT_DIR}/${solver_name}"

    for stats_file in "${OUTPUT_DIR}"/*.stats; do
        if [ -f "${stats_file}" ]; then
            benchmark=$(basename "${stats_file}" .stats)
            exit_status=$(grep "EXIT_STATUS=" "${stats_file}" | cut -d= -f2)
            wall_time=$(grep "Elapsed" "${stats_file}" | awk '{print $8}')
            user_time=$(grep "User time" "${stats_file}" | awk '{print $4}')
            sys_time=$(grep "System time" "${stats_file}" | awk '{print $4}')
            peak_mem=$(grep "Maximum resident set size" "${stats_file}" | awk '{print $6}')

            echo "${solver_name},${benchmark},${exit_status},${wall_time},${user_time},${sys_time},${peak_mem}" >> "${SUMMARY_FILE}"
        fi
    done
done

echo "Execution completed at $(date)" >> "${MAIN_LOG}"
