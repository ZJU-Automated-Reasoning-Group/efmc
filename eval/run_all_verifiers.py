"""
Running all verifiers (efmc and other third-party verifiers)

Example configuration file (benchmark_config.ini):
[SOLVERS]
z3_path = ${Z3_ROOT}/bin/z3
z3_options = fp.engine=spacer
eldarica_path = ${ELDARICA_ROOT}/eld
efmc_path = ${EFMC_ROOT}/efmc # really?

We also have a default configuration inside the script.
"""

#!/usr/bin/env python3
import os
import sys
import time
import subprocess
from datetime import datetime
from pathlib import Path
import csv
from concurrent.futures import ProcessPoolExecutor
import re
import argparse
import configparser
import logging


class BenchmarkConfig:
    def __init__(self):
        self.parse_arguments()
        self.load_config()
        self.setup_logging()

    def parse_arguments(self):
        parser = argparse.ArgumentParser(description='Benchmark Runner for SMT Solvers')
        parser.add_argument('--config', default='benchmark_config.ini',
                            help='Path to configuration file')
        parser.add_argument('--benchmark-dir', required=True,
                            help='Directory containing benchmark files')
        parser.add_argument('--timeout', type=int, required=True,
                            help='Timeout in seconds for each benchmark')
        parser.add_argument('--parallel', type=int, default=4,
                            help='Number of parallel jobs')
        parser.add_argument('--output-dir', default='./results',
                            help='Base directory for output files')

        self.args = parser.parse_args()

    def load_config(self):
        config = configparser.ConfigParser()

        # Default configuration
        default_config = {
            'SOLVERS': {
                'z3_path': '${Z3_ROOT}/bin/z3',
                'z3_options': 'fp.engine=spacer',
                'eldarica_path': '${ELDARICA_ROOT}/eld',
                'eldarica_options': ''
            }
        }

        # Create default config file if it doesn't exist
        if not os.path.exists(self.args.config):
            config.read_dict(default_config)
            with open(self.args.config, 'w') as configfile:
                config.write(configfile)

        config.read(self.args.config)

        # Process solver configurations
        self.solvers = []
        solver_section = config['SOLVERS']
        for i in range(0, len(solver_section), 2):
            keys = list(solver_section.keys())
            if i + 1 < len(keys):
                path_key = keys[i]
                options_key = keys[i + 1]
                if path_key.endswith('_path') and options_key.endswith('_options'):
                    path = os.path.expandvars(solver_section[path_key])
                    options = solver_section[options_key]
                    self.solvers.append((path, options))

        # Setup other configurations
        self.benchmark_dir = self.args.benchmark_dir
        self.timeout = self.args.timeout
        self.num_parallel = self.args.parallel
        self.output_root = os.path.expanduser(self.args.output_dir)

        # Create timestamp-based output directory
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.base_output_dir = os.path.join(self.output_root, timestamp)
        os.makedirs(self.base_output_dir, exist_ok=True)

        # Setup log file path
        self.log_file = os.path.join(self.base_output_dir, "execution.log")

    def setup_logging(self):
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(levelname)s - %(message)s',
            handlers=[
                logging.FileHandler(self.log_file),
                logging.StreamHandler()
            ]
        )


def run_benchmark(args):
    solver_path, solver_options, input_file, output_dir = args
    filename = os.path.basename(input_file)
    solver_name = os.path.basename(solver_path)
    log_file = os.path.join(output_dir, filename)
    stats_file = f"{log_file}.stats"

    logging.info(f"Running {solver_name} on {filename}")

    # Run solver with timeout and capture time/memory usage
    time_cmd = ['/usr/bin/time', '-v']
    solver_cmd = [solver_path] + (solver_options.split() if solver_options else [])
    cmd = ['timeout', str(config.timeout)] + time_cmd + solver_cmd + [input_file]

    try:
        with open(f"{log_file}.out", 'w') as out_file, \
                open(f"{log_file}.err", 'w') as err_file:
            process = subprocess.run(cmd, stdout=out_file, stderr=err_file)

        # Write stats
        with open(stats_file, 'w') as f:
            f.write(f"EXIT_STATUS={process.returncode}\n")

            # Extract stats from time output
            with open(f"{log_file}.err", 'r') as err_file:
                err_content = err_file.read()
                for metric in ["Maximum resident set size", "User time",
                               "System time", "Elapsed (wall clock) time"]:
                    match = re.search(f"{metric}.*", err_content)
                    if match:
                        f.write(f"{match.group()}\n")

    except Exception as e:
        logging.error(f"Error running benchmark {filename}: {str(e)}")


def main():
    global config
    config = BenchmarkConfig()

    logging.info(f"Benchmark directory: {config.benchmark_dir}")
    logging.info(f"Timeout: {config.timeout}")
    logging.info(f"Number of parallel jobs: {config.num_parallel}")

    # Process each solver
    summary_data = []
    for solver_path, solver_options in config.solvers:
        solver_name = os.path.basename(solver_path)
        output_dir = os.path.join(config.base_output_dir, solver_name)
        os.makedirs(output_dir, exist_ok=True)

        logging.info(f"Processing solver: {solver_name}")
        logging.info(f"Options: {solver_options}")

        # Find all benchmark files
        benchmark_files = list(Path(config.benchmark_dir).glob("*.smt2"))

        # Run benchmarks in parallel
        with ProcessPoolExecutor(max_workers=config.num_parallel) as executor:
            args_list = [(solver_path, solver_options, str(f), output_dir)
                         for f in benchmark_files]
            executor.map(run_benchmark, args_list)

        # Collect results for summary
        for stats_file in Path(output_dir).glob("*.stats"):
            if stats_file.is_file():
                benchmark = stats_file.stem
                stats = {}
                with open(stats_file) as f:
                    for line in f:
                        if line.startswith("EXIT_STATUS="):
                            stats['exit_status'] = line.split('=')[1].strip()
                        elif "Elapsed" in line:
                            stats['wall_time'] = line.split()[7]
                        elif "User time" in line:
                            stats['user_time'] = line.split()[3]
                        elif "System time" in line:
                            stats['sys_time'] = line.split()[3]
                        elif "Maximum resident set size" in line:
                            stats['peak_mem'] = line.split()[5]

                summary_data.append({
                    'Solver': solver_name,
                    'Benchmark': benchmark,
                    'Exit Status': stats.get('exit_status', ''),
                    'Wall Time': stats.get('wall_time', ''),
                    'User Time': stats.get('user_time', ''),
                    'System Time': stats.get('sys_time', ''),
                    'Peak Memory': stats.get('peak_mem', '')
                })

    # Write summary CSV
    summary_file = os.path.join(config.base_output_dir, "summary.csv")
    fieldnames = ['Solver', 'Benchmark', 'Exit Status', 'Wall Time',
                  'User Time', 'System Time', 'Peak Memory']
    with open(summary_file, 'w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(summary_data)

    logging.info(f"Execution completed at {datetime.now()}")


if __name__ == "__main__":
    main()
