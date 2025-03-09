"""
TODO: by LLM, to be checked.
Regression script for runnig all SMT solvers on all benchmarks in the given directory.
"""
import csv
import concurrent.futures
import argparse
import os
import subprocess
import time
from typing import Dict, List, Tuple


class Solver:
    def __init__(self, name: str, command: str):
        self.name = name
        self.command = command

    def run(self, input_file: str, timeout: int) -> Tuple[float, float, bool, str]:
        """
        Run the solver on the given input file with the given timeout.
        """
        start_time = time.time()
        result = subprocess.run(
            [self.command, input_file],
            capture_output=True,
            text=True,
            timeout=timeout
        )
        end_time = time.time()
        memory = result.memory_info().rss / 1024 / 1024  # Convert to MB
        timeout = result.timeout
        output = result.stdout
        return end_time - start_time, memory, timeout, output


def load_config(config_file: str) -> Dict[str, List[Solver]]:
    """
    Load the configuration from the given file.
    """
    config = {}
    with open(config_file, 'r') as f:
        for line in f:
            if line.strip() == '':
                continue
            name, command = line.strip().split('=')
            config[name] = command
    return config


def run_solver(solver: Solver, input_file: str, timeout: int) -> Tuple[float, float, bool, str]:
    """
    Run the solver on the given input file with the given timeout.
    """
    return solver.run(input_file, timeout)


def run_all_solvers(config: Dict[str, List[Solver]], benchmark_dir: str, output_dir: str, timeout: int, parallel: int):
    """
    Run all solvers on all benchmarks in the given directory.
    """
    # Get all benchmark files
    benchmark_files = []
    for root, dirs, files in os.walk(benchmark_dir):
        for file in files:
            if file.endswith('.smt2'):
                benchmark_files.append(os.path.join(root, file))
    
    # Run solvers in parallel
    with concurrent.futures.ThreadPoolExecutor(max_workers=parallel) as executor:
        futures = [executor.submit(run_solver, solver, benchmark_file, timeout) for solver in config.values() for benchmark_file in benchmark_files]
        results = [future.result() for future in concurrent.futures.as_completed(futures)]
    
    # Write results to output file
    with open(os.path.join(output_dir, 'results.csv'), 'w') as f:
        writer = csv.writer(f)
        writer.writerow(['Benchmark', 'Solver', 'Time', 'Memory', 'Timeout', 'Output'])
        for result in results:
            writer.writerow(result)

def run_solvers(config: Dict[str, List[Solver]], benchmark_dir: str, output_dir: str, timeout: int, parallel: int):
    """
    Run all solvers on all benchmarks in the given directory.
    """
    run_all_solvers(config, benchmark_dir, output_dir, timeout, parallel)


def main():
    parser = argparse.ArgumentParser(description='Run all SMT solvers on all benchmarks in the given directory.')
    parser.add_argument('--benchmark-dir', type=str, required=True, help='Path to the directory containing the benchmarks')
    parser.add_argument('--timeout', type=int, default=300, help='Timeout for each solver in seconds')
    parser.add_argument('--parallel', type=int, default=4, help='Number of parallel solvers')
    parser.add_argument('--output-dir', type=str, default='./results', help='Path to the output directory')
    args = parser.parse_args()

    # Load configuration
    config = load_config(args.config_file)

    # Run solvers
    run_solvers(config, args.benchmark_dir, args.output_dir, args.timeout, args.parallel)

if __name__ == '__main__':
    main()  