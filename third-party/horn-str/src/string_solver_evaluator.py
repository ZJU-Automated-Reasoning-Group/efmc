import os
import subprocess
import time
import csv
import argparse
import json
import random
from collections import defaultdict
from statistics import mean

def load_config(config_path="config.json"):
    """Load solver configurations from config.json file."""
    if not os.path.exists(config_path):
        print(f"Warning: Config file {config_path} not found. Using command-line arguments only.")
        return {}
    
    try:
        with open(config_path, 'r') as f:
            # Remove comments if present (JSON doesn't support comments)
            content = ""
            for line in f:
                if not line.strip().startswith("//"):
                    content += line
            
            config = json.loads(content)
        
        # Extract solver configurations
        solver_configs = {}
        for solver, config_data in config.items():
            if "bin" in config_data and isinstance(config_data["bin"], list) and len(config_data["bin"]) > 0:
                # First element is the path, rest are default arguments
                solver_configs[solver] = {
                    "path": config_data["bin"][0],
                    "args": config_data["bin"][1:] if len(config_data["bin"]) > 1 else []
                }
        
        return solver_configs
    except json.JSONDecodeError as e:
        print(f"Error: Config file {config_path} is not valid JSON: {str(e)}")
        return {}
    except Exception as e:
        print(f"Error loading config: {str(e)}")
        return {}

def run_solver_on_files(source_dir, solver_type, binary_config, csv_output, timeout_seconds=60, reachable_only=False, random_sample=0):
    """
    Run a specified solver on all .smt2 files in the source directory.
    """
    # Extract binary path and default arguments
    binary_path = binary_config["path"]
    default_args = binary_config["args"]
    
    # Create a list to store all file paths with the results
    results = []
    
    # Counter for different benchmark types
    benchmark_counts = {
        "incremental_equiv": 0,
        "incremental_reach": 0,
        "non_incremental_equiv": 0,
        "non_incremental_reach": 0
    }
    
    # Counter for skipped files
    skipped_files = 0
    
    # Helper function to check if a file should be processed
    def should_process_file(file_path):
        # First check if the file contains (check-sat)
        try:
            with open(file_path, 'r') as f:
                content = f.read()
                if "(check-sat)" not in content:
                    print(f"Skipping file (no check-sat): {os.path.basename(file_path)}")
                    # Remove the file as requested
                    try:
                        os.remove(file_path)
                        print(f"Removed file: {os.path.basename(file_path)}")
                    except OSError as e:
                        print(f"Error removing file {file_path}: {e}")
                    nonlocal skipped_files
                    skipped_files += 1
                    return False
        except Exception as e:
            print(f"Error reading file {file_path}: {e}")
            return False
        
        # Next check reachable_only constraint
        if reachable_only and not os.path.basename(file_path).startswith("reach"):
            return False
        
        # If random sampling is enabled, apply it by returning True with probability random_sample/100
        if random_sample > 0:
            return random.random() < (random_sample / 100.0)
        
        # If no filters are active, process all files
        return True
    
    # Helper function to update benchmark counters
    def update_benchmark_count(file_path, is_incremental):
        filename = os.path.basename(file_path)
        if filename.startswith("equiv"):
            if is_incremental:
                benchmark_counts["incremental_equiv"] += 1
            else:
                benchmark_counts["non_incremental_equiv"] += 1
        elif filename.startswith("reach"):
            if is_incremental:
                benchmark_counts["incremental_reach"] += 1
            else:
                benchmark_counts["non_incremental_reach"] += 1
    
    # Check if source_dir is a direct path to an SMT2 file
    if source_dir.endswith(".smt2") and os.path.isfile(source_dir):
        if should_process_file(source_dir):
            # Count the benchmark (assume non-incremental for single files)
            update_benchmark_count(source_dir, False)
            
            result_data = run_single_benchmark(source_dir, solver_type, binary_path, default_args, timeout_seconds)
            results.append(result_data)
    else:
        # Check if the directory contains .smt2 files directly
        smt2_files = [f for f in os.listdir(source_dir) if f.endswith(".smt2")]
        if smt2_files:
            print(f"Processing {len(smt2_files)} .smt2 files in root directory")
            for file in smt2_files:
                file_path = os.path.join(source_dir, file)
                if should_process_file(file_path):
                    # Count the benchmark (assume non-incremental for root files)
                    update_benchmark_count(file_path, False)
                    
                    result_data = run_single_benchmark(file_path, solver_type, binary_path, default_args, timeout_seconds)
                    results.append(result_data)
        
        # Process all subdirectories 
        for subdir in [d for d in os.listdir(source_dir) if os.path.isdir(os.path.join(source_dir, d))]:
            subdir_path = os.path.join(source_dir, subdir)
            
            # Check for non_incremental and incremental directories
            for dir_type in ["non_incremental", "incremental"]:
                type_path = os.path.join(subdir_path, dir_type)
                
                if os.path.isdir(type_path):
                    print(f"Processing {subdir}/{dir_type}")
                    # Set is_incremental flag based on directory type
                    is_incremental = (dir_type == "incremental")
                    # Process all SMT2 files in this specific directory
                    for file in os.listdir(type_path):
                        if file.endswith(".smt2"):
                            file_path = os.path.join(type_path, file)
                            if should_process_file(file_path):
                                # Count the benchmark
                                update_benchmark_count(file_path, is_incremental)
                                
                                result_data = run_single_benchmark(
                                    file_path, 
                                    solver_type, 
                                    binary_path, 
                                    default_args, 
                                    timeout_seconds,
                                    is_incremental
                                )
                                results.append(result_data)
            
            # Check if the subdirectory itself contains SMT2 files
            smt2_in_subdir = [f for f in os.listdir(subdir_path) if f.endswith(".smt2")]
            if smt2_in_subdir:
                print(f"Processing {len(smt2_in_subdir)} .smt2 files in {subdir}")
                for file in smt2_in_subdir:
                    file_path = os.path.join(subdir_path, file)
                    if should_process_file(file_path):
                        # Count the benchmark (assume non-incremental for files not in specific directories)
                        update_benchmark_count(file_path, False)
                        
                        # Assume non-incremental for files not in specific directories
                        result_data = run_single_benchmark(file_path, solver_type, binary_path, default_args, timeout_seconds)
                        results.append(result_data)
    
    # Print benchmark type statistics
    print("\nBenchmark Type Statistics:")
    print("-" * 60)
    print(f"Incremental Equivalence: {benchmark_counts['incremental_equiv']}")
    print(f"Incremental Reachability: {benchmark_counts['incremental_reach']}")
    print(f"Non-Incremental Equivalence: {benchmark_counts['non_incremental_equiv']}")
    print(f"Non-Incremental Reachability: {benchmark_counts['non_incremental_reach']}")
    total_benchmarks = sum(benchmark_counts.values())
    print(f"Total: {total_benchmarks}")
    
    # Write results to a CSV file
    with open(csv_output, mode='w', newline='') as csv_file:
        csv_writer = csv.writer(csv_file)
        csv_writer.writerow(["File", "Time", "Result"])  # Write header
        csv_writer.writerows(results)  # Write all file results

    print(f"Results have been written to {csv_output}")
    return results
def run_single_benchmark(file_path, solver_type, binary_path, default_args, timeout_seconds, is_incremental=False):
    """Run a single benchmark file with the specified solver."""
    # Extract more context from the path (last two directories + filename)
    path_parts = file_path.split(os.sep)
    if len(path_parts) >= 3:
        context_path = os.path.join(path_parts[-3], path_parts[-2], path_parts[-1])
    elif len(path_parts) >= 2:
        context_path = os.path.join(path_parts[-2], path_parts[-1])
    else:
        context_path = path_parts[-1]
    
    incremental_str = " (incremental)" if is_incremental else ""
    print(f"Running {solver_type}{incremental_str} on: {context_path}")
    start_time = time.time()
    
    # Start with the binary path and its default arguments
    command = [binary_path] + default_args.copy()  # Create a copy to avoid modifying the original

    # Add appropriate incremental flags if needed and not already present
    if is_incremental:
        if solver_type.lower() == "cvc5" and not any(arg.startswith("--incremental") for arg in command):
            command.append("--incremental")
        elif solver_type.lower() in ["z3", "z3-alpha", "z3-noodler"] and "-smt2" not in command:
            command.append("-smt2")
    
    # Initialize process to None
    process = None
    
    # Add solver-specific arguments if needed
    if solver_type.lower() == "ostrich":
        if "+stdin" not in default_args:
            # If not using stdin mode, add file path directly
            command.append(file_path)
        
        # Check if we need to add timeout argument
        if not any(arg.startswith("-timeout=") for arg in command):
            command.append(f"-timeout={timeout_seconds * 1000}")
        
        try:
            if "+stdin" in default_args:
                # Use stdin mode
                with open(file_path, 'r') as f:
                    file_content = f.read()
                
                process = subprocess.Popen(
                    command,
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE
                )
                
                stdout, stderr = process.communicate(
                    input=file_content.encode(),
                    timeout=timeout_seconds
                )
            else:
                # Use file path mode
                process = subprocess.Popen(
                    command,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE
                )
                
                stdout, stderr = process.communicate(timeout=timeout_seconds)
            
            elapsed_time = time.time() - start_time
            
            # Decode the output
            output = stdout.decode().strip().lower()

            # Determine the result
            if "unsat" in output:
                result = "unsat"
            elif "sat" in output:
                result = "sat"
            else:
                result = "unknown"
        
        except subprocess.TimeoutExpired:
            # Handle timeout: terminate the process
            if process is not None:
                process.terminate()
                try:
                    # Give the process some time to terminate gracefully
                    process.wait(5)
                except subprocess.TimeoutExpired:
                    # Force kill if it doesn't terminate
                    process.kill()

            elapsed_time = float(timeout_seconds)
            result = "timeout"

        except Exception as e:
            # Handle any other unexpected errors
            elapsed_time = 0.0
            result = f"error: {str(e)}"
            
    elif solver_type.lower() in ["z3", "z3-alpha", "z3-noodler"]:
        # Z3 variants
        uses_stdin = "-in" in default_args
        
        if not uses_stdin:
            # If not using stdin, add file path
            command.append(file_path)

        try:
            if uses_stdin:
                # Read file and send to stdin
                with open(file_path, 'r') as f:
                    file_content = f.read()
                
                process = subprocess.Popen(
                    command,
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE
                )
                
                stdout, stderr = process.communicate(
                    input=file_content.encode(),
                    timeout=timeout_seconds
                )
            else:
                # Standard execution with file path
                process = subprocess.run(
                    command,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    timeout=timeout_seconds
                )
                
                stdout = process.stdout
                stderr = process.stderr
            
            # Capture time taken
            elapsed_time = time.time() - start_time

            # Decode the output
            output = stdout.decode().strip().lower()
            
            # Determine the result
            if "unsat" in output:
                result = "unsat"
            elif "sat" in output:
                result = "sat"
            else:
                result = "unknown"
                
        except subprocess.TimeoutExpired:
            # Handle timeout: terminate the process only if it's a Popen object
            if process is not None and hasattr(process, 'terminate'):
                process.terminate()
                try:
                    # Give the process some time to terminate gracefully
                    process.wait(5)
                except subprocess.TimeoutExpired:
                    # Force kill if it doesn't terminate
                    process.kill()

            elapsed_time = float(timeout_seconds)
            result = "timeout"
            
        except Exception as e:
            elapsed_time = 0.0
            result = f"error: {str(e)}"
            
    else:  # CVC5 or other solver
        # Add the file path at the end
        command.append(file_path)
        
        try:
            # Use subprocess.run for simpler execution
            process = subprocess.run(
                command,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=timeout_seconds
            )
            
            # Capture time taken
            elapsed_time = time.time() - start_time

            # Get the output
            output = process.stdout.decode().strip().lower()

            # Check result
            if "unsat" in output:
                result = "unsat"
            elif "sat" in output:
                result = "sat"
            else:
                result = "unknown"
                
        except subprocess.TimeoutExpired:
            # For subprocess.run, we don't need to terminate the process 
            # as it's handled automatically by the run method when timeout occurs
            elapsed_time = float(timeout_seconds)
            result = "timeout"
            
        except Exception as e:
            elapsed_time = 0.0
            result = f"error: {str(e)}"
    
    # Return the result data
    return [file_path, elapsed_time, result]

def display_results_summary(result_files):
    """Display a summary of all benchmark results."""
    print("\n" + "="*80)
    print("BENCHMARK RESULTS SUMMARY")
    print("="*80)
    
    all_results = []
    solver_stats = {}
    
    # For category breakdown
    category_stats = {
        "incremental_equiv": {"total": 0, "solved": 0, "time": 0.0},
        "incremental_reach": {"total": 0, "solved": 0, "time": 0.0},
        "non_incremental_equiv": {"total": 0, "solved": 0, "time": 0.0},
        "non_incremental_reach": {"total": 0, "solved": 0, "time": 0.0}
    }
    
    # Process each results file
    for solver_type, csv_file in result_files.items():
        if not os.path.exists(csv_file):
            print(f"No results file found for {solver_type}")
            continue
            
        results = []
        with open(csv_file, 'r', newline='') as f:
            reader = csv.reader(f)
            next(reader)  # Skip header
            for row in reader:
                results.append(row)
        
        # Compute statistics
        total = len(results)
        if total == 0:
            print(f"No results found for {solver_type}")
            continue
            
        stats = defaultdict(int)
        times = []
        total_time = 0.0
        
        for file_path, time_str, result in results:
            # Categorize the result
            is_incremental = "/incremental/" in file_path
            filename = os.path.basename(file_path)
            
            # Determine category
            if filename.startswith("equiv"):
                category = "incremental_equiv" if is_incremental else "non_incremental_equiv"
            elif filename.startswith("reach"):
                category = "incremental_reach" if is_incremental else "non_incremental_reach"
            else:
                # Skip files that don't match our naming pattern
                continue
                
            # Update category stats
            category_stats[category]["total"] += 1
            if result in ["sat", "unsat"]:
                category_stats[category]["solved"] += 1
            
            try:
                time_val = float(time_str)
                category_stats[category]["time"] += time_val
            except (ValueError, TypeError):
                pass
            
            # Update overall stats
            stats[result] += 1
            try:
                time_val = float(time_str)
                times.append(time_val)
                total_time += time_val
            except (ValueError, TypeError):
                pass
        
        # Calculate time statistics
        avg_time = mean(times) if times else 0
        max_time = max(times) if times else 0
        
        # Save stats
        solver_stats[solver_type] = {
            "total": total,
            "sat": stats["sat"],
            "unsat": stats["unsat"],
            "unknown": stats["unknown"],
            "timeout": stats["timeout"],
            "error": sum(1 for r in stats.keys() if r.startswith("error")),
            "avg_time": avg_time,
            "max_time": max_time,
            "total_time": total_time
        }
        
        all_results.extend(results)
    
    # Print summary table
    print("\nSolver Statistics:")
    print("-" * 120)
    print(f"{'Solver':<15} | {'Total':<8} | {'SAT':<8} | {'UNSAT':<8} | {'Unknown':<8} | {'Timeout':<8} | {'Error':<8} | {'Avg Time':<10} | {'Max Time':<10} | {'Total Time':<10}")
    print("-" * 120)
    
    for solver, stats in solver_stats.items():
        print(f"{solver:<15} | {stats['total']:<8} | {stats['sat']:<8} | {stats['unsat']:<8} | {stats['unknown']:<8} | {stats['timeout']:<8} | {stats['error']:<8} | {stats['avg_time']:<10.2f} | {stats['max_time']:<10.2f} | {stats['total_time']:<10.2f}")
    
    # Print category breakdown
    print("\nCategory Breakdown:")
    print("-" * 95)
    print(f"{'Category':<25} | {'Total':<10} | {'Solved':<10} | {'Success %':<10} | {'Total Time':<15} | {'Avg Time':<10}")
    print("-" * 95)
    
    for category, stats in category_stats.items():
        if stats["total"] > 0:
            success_percent = (stats["solved"] / stats["total"]) * 100
            avg_time = stats["time"] / stats["total"] if stats["total"] > 0 else 0
            print(f"{category:<25} | {stats['total']:<10} | {stats['solved']:<10} | {success_percent:<10.1f} | {stats['time']:<15.2f} | {avg_time:<10.2f}")
    
    # Calculate overall statistics
    if all_results:
        total_benchmarks = len(all_results)
        completed = sum(1 for _, _, r in all_results if r in ["sat", "unsat"])
        timeouts = sum(1 for _, _, r in all_results if r == "timeout")
        errors = sum(1 for _, _, r in all_results if r.startswith("error"))
        
        # Calculate overall total time
        overall_total_time = 0.0
        for _, time_str, _ in all_results:
            try:
                overall_total_time += float(time_str)
            except (ValueError, TypeError):
                pass
        
        print("\nOverall Statistics:")
        print(f"Total benchmarks: {total_benchmarks}")
        print(f"Completed: {completed} ({completed/total_benchmarks*100:.1f}%)")
        print(f"Timeouts: {timeouts} ({timeouts/total_benchmarks*100:.1f}%)")
        print(f"Errors: {errors} ({errors/total_benchmarks*100:.1f}%)")
        print(f"Total execution time: {overall_total_time:.2f} seconds ({overall_total_time/60:.2f} minutes)")
    
    print("\nResults files:")
    for solver, csv_file in result_files.items():
        print(f"  {solver}: {csv_file}")
    
    print("="*80)
    
def main():
    parser = argparse.ArgumentParser(description="Run benchmarks with multiple solvers")
    parser.add_argument("--source", required=True, help="Source directory with benchmark files")
    parser.add_argument("--config", default="config.json", help="Path to config.json file with solver paths")
    parser.add_argument("--timeout", type=int, default=60, help="Timeout in seconds (default: 60)")
    parser.add_argument("--output-prefix", default="", help="Prefix for output CSV files")
    parser.add_argument("--solvers", help="Comma-separated list of solvers to run (e.g., 'ostrich,cvc5,z3')")
    parser.add_argument("--summary-only", action="store_true", help="Only display summary of existing results")
    parser.add_argument("--reachable-only", action="store_true", help="Only process files starting with 'reach'")
    parser.add_argument("--random-sample", type=float, default=0, help="Randomly sample specified percentage (e.g., 10 for 10%) of benchmarks")

    args = parser.parse_args()
    
    # Dictionary to track result files
    result_files = {}
    
    # If not summary only, run benchmarks
    if not args.summary_only:
        # Load config file
        solver_configs = load_config(args.config)
        
        # Create output prefix if provided
        prefix = args.output_prefix + "_" if args.output_prefix else ""
        
        # Determine which solvers to run
        solvers_to_run = []
        if args.solvers:
            solvers_to_run = [s.strip().lower() for s in args.solvers.split(',')]
        
        # Track if any solvers were actually run
        solvers_run = False
        
        # Run benchmarks with each configured solver
        for solver_type, config in solver_configs.items():
            if not solvers_to_run or solver_type.lower() in solvers_to_run:
                if not os.path.exists("out"):
                    os.makedirs("out")
                output_file = f"out/{prefix}{solver_type}_results.csv"
                result_files[solver_type] = output_file
                
                print(f"\n=== Running {solver_type} benchmarks ===")
                print(f"Using binary: {config['path']}")
                print(f"Default args: {' '.join(config['args'])}")
                
                if args.random_sample > 0:
                    print(f"Using random sampling: {args.random_sample}% of benchmarks")
                
                run_solver_on_files(
                    args.source, 
                    solver_type, 
                    config, 
                    output_file,
                    args.timeout,
                    args.reachable_only,
                    args.random_sample
                )
                solvers_run = True
        
        if not solvers_run:
            print("Error: No configured solvers were found in the config file or matched the specified solvers")
            parser.print_help()
            return
    else:
        # Just load existing result files for summary
        prefix = args.output_prefix + "_" if args.output_prefix else ""
        if args.solvers:
            for solver in args.solvers.split(','):
                solver = solver.strip()
                # check if the out folder exists
                if not os.path.exists("out"):
                    os.makedirs("out")
                result_files[solver] = f"out/{prefix}{solver}_results.csv"
        else:
            # Try to find all result files in current directory
            if os.path.exists("out"):
                for file in os.listdir("out"):
                    if file.endswith('_results.csv'):
                        solver = file.replace(prefix, '').replace('_results.csv', '')
                        result_files[solver] = os.path.join("out", file)
    
    # Display summary of results
    display_results_summary(result_files)

if __name__ == "__main__":
    main()