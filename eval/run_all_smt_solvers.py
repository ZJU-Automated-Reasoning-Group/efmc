# coding: utf-8
import csv
import os
import subprocess
import time
import argparse
import sys
from multiprocessing.pool import Pool
import signal
from threading import Timer
import logging
from datetime import datetime
from typing import Dict, List, Tuple
import psutil
import json


class Solver:
    def __init__(self, name: str, command: str):
        self.name = name
        self.command = command


class SolverResult:
    def __init__(self, runtime: float, memory: float, timeout: bool, error: str = None, output: str = None):
        self.runtime = runtime
        self.memory = memory  # Peak memory in MB
        self.timeout = timeout
        self.error = error
        self.output = output


def parse_arguments():
    parser = argparse.ArgumentParser(description='Multi-solver SMT benchmark runner')
    parser.add_argument('--output', dest='output', default='~/tmp/res', type=str,
                        help='Output directory for results')
    parser.add_argument('--timeout', dest='timeout', default=30, type=int,
                        help='Timeout for each solving attempt (seconds)')
    parser.add_argument('--workers', dest='workers', default=1, type=int,
                        help='Number of parallel workers')
    parser.add_argument('--dir', dest='dir', required=True, type=str,
                        help='Directory containing SMT2 files')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='Increase output verbosity')
    parser.add_argument('--config', type=str, default='solvers.json',
                        help='JSON configuration file for solvers')
    return parser.parse_args()


def setup_logging(verbose: bool, output_dir: str):
    log_level = logging.DEBUG if verbose else logging.INFO
    log_file = os.path.join(output_dir, f'benchmark_{datetime.now():%Y%m%d_%H%M%S}.log')
    logging.basicConfig(
        level=log_level,
        format='%(asctime)s - %(levelname)s - %(message)s',
        handlers=[
            logging.FileHandler(log_file),
            logging.StreamHandler()
        ]
    )


def load_solvers(config_file: str) -> List[Solver]:
    try:
        with open(config_file) as f:
            config = json.load(f)
        return [Solver(solver['name'], solver['command']) for solver in config['solvers']]
    except Exception as e:
        logging.error(f"Failed to load solver configuration: {e}")
        sys.exit(1)


def find_smt2(path: str) -> List[str]:
    try:
        return [os.path.join(root, f) for root, _, files in os.walk(path)
                for f in files if f.endswith('.smt2')]
    except Exception as e:
        logging.error(f"Error while searching for SMT2 files: {e}")
        return []


def get_process_memory(process) -> float:
    try:
        process = psutil.Process(process.pid)
        return process.memory_info().rss / 1024 / 1024  # Convert to MB
    except:
        return 0.0


def run_solver(solver: Solver, input_file: str, timeout: int) -> SolverResult:
    cmd = solver.command.split() + ['--file', input_file]
    is_timeout = False
    start_time = time.time()
    try:
        process = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            preexec_fn=os.setsid
        )

        timer = Timer(timeout, lambda p: os.killpg(p.pid, signal.SIGTERM), [process])
        timer.start()

        try:
            stdout, stderr = process.communicate(timeout=timeout)
            peak_memory = get_process_memory(process)
            output = stdout.decode('utf-8')
            error = stderr.decode('utf-8') if stderr else None
        except subprocess.TimeoutExpired:
            is_timeout = True
            os.killpg(process.pid, signal.SIGTERM)
            process.kill()
            output = "TIMEOUT"
            error = "Solver exceeded time limit"
            peak_memory = get_process_memory(process)
        finally:
            timer.cancel()

        runtime = time.time() - start_time
        return SolverResult(runtime, peak_memory, is_timeout, error, output)

    except Exception as e:
        logging.error(f"Error running solver {solver.name} on {input_file}: {e}")
        return SolverResult(0.0, 0.0, False, str(e))


def solve_formulas(args: Tuple[List[str], List[Solver], int]) -> Dict:
    files, solvers, timeout = args
    results = {}
    for input_file in files:
        file_results = {}
        for solver in solvers:
            logging.debug(f"Running {solver.name} on {input_file}")
            result = run_solver(solver, input_file, timeout)
            file_results[solver.name] = result
        results[input_file] = file_results
    return results


def write_results(results: List[Dict], output_dir: str, solvers: List[Solver]):
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_file = os.path.join(output_dir, f'results_{timestamp}.csv')

    headers = ['File'] + [f'{s.name}_time,{s.name}_memory,{s.name}_timeout,{s.name}_error'
                          for s in solvers]

    with open(output_file, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(headers)

        for result_dict in results:
            for input_file, solver_results in result_dict.items():
                row = [input_file]
                for solver in solvers:
                    result = solver_results.get(solver.name)
                    if result:
                        row.extend([
                            f"{result.runtime:.2f}",
                            f"{result.memory:.2f}",
                            str(result.timeout),
                            result.error or ''
                        ])
                writer.writerow(row)

    logging.info(f"Results written to {output_file}")


def main():
    args = parse_arguments()

    # Create output directory
    os.makedirs(args.output, exist_ok=True)

    # Setup logging
    setup_logging(args.verbose, args.output)

    # Load solver configurations
    solvers = load_solvers(args.config)
    logging.info(f"Loaded {len(solvers)} solvers")

    # Find SMT2 files
    files = find_smt2(args.dir)
    logging.info(f"Found {len(files)} SMT2 files")

    # Split files for parallel processing
    chunks = [files[i::args.workers] for i in range(args.workers)]

    # Create process pool
    with Pool(args.workers) as pool:
        try:
            results = pool.map(solve_formulas,
                               [(chunk, solvers, args.timeout) for chunk in chunks])

            # Write results
            write_results(results, args.output, solvers)

        except KeyboardInterrupt:
            pool.terminate()
            logging.info("Benchmark interrupted by user")
            sys.exit(1)
        except Exception as e:
            logging.error(f"Error during benchmark execution: {e}")
            pool.terminate()
            sys.exit(1)
        finally:
            pool.close()
            pool.join()


if __name__ == "__main__":
    main()
