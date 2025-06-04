"""
Running different configurations of efmc
"""
import logging
import argparse
import concurrent.futures
import json
import os
import subprocess
import sys
import time
from typing import List, Dict
import signal


# Set up logging
def setup_logging(log_level=logging.INFO):
    logger = logging.getLogger('efmc_verifier')
    logger.setLevel(log_level)
    
    # Create console handler
    console_handler = logging.StreamHandler()
    console_handler.setLevel(log_level)
    
    # Create formatter
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    console_handler.setFormatter(formatter)
    
    # Add handler to logger
    logger.addHandler(console_handler)
    
    return logger


class SolverConfig:
    def __init__(self, engine: str, template: str = None, aux_inv: bool = False, lang: str = "sygus", additional_opts: List[str] = None):
        self.engine = engine
        self.template = template
        self.aux_inv = aux_inv
        self.lang = lang
        self.additional_opts = additional_opts or []

    def get_command_args(self) -> List[str]:
        cmd = ["--engine", self.engine]
        if self.template:
            cmd.extend(["--template", self.template])
        # Only add --kind-aux-inv flag if aux_inv is True
        if self.aux_inv:
            cmd.append("--kind-aux-inv")
        cmd.extend(["--lang", self.lang])
        cmd.extend(self.additional_opts)
        return cmd


def load_config(config_file: str) -> Dict[str, List[SolverConfig]]:
    logger = logging.getLogger('efmc_verifier')
    logger.info(f"Loading configuration from {config_file}")
    
    with open(config_file) as f:
        data = json.load(f)

    configs = {}
    for name, cfg in data.items():
        configs[name] = [
            SolverConfig(
                engine=c.get("engine"),
                template=c.get("template"),
                aux_inv=c.get("aux_inv", False),
                lang=c.get("lang", "chc"),
                additional_opts=c.get("additional_opts", [])
            ) for c in cfg
        ]
    
    logger.info(f"Loaded {len(configs)} configuration groups")
    return configs


def run_solver(solver_path: str, config: SolverConfig, input_file: str,
               timeout: int) -> tuple:
    logger = logging.getLogger('efmc_verifier')
    start_time = time.time()
    cmd = [solver_path] + config.get_command_args() + ["--file", input_file]
    
    logger.debug(f"Running command: {' '.join(cmd)}")
    
    try:
        # Create a new process group with unique group ID
        process = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            preexec_fn=os.setsid
        )
        pgid = os.getpgid(process.pid)
        
        try:
            stdout, stderr = process.communicate(timeout=timeout)
            elapsed = time.time() - start_time
            retcode = process.returncode
            
        except subprocess.TimeoutExpired:
            # Kill only processes in our process group
            try:
                # First try a gentle termination
                os.killpg(pgid, signal.SIGTERM)
                
                # Give it a short time to terminate gracefully
                for _ in range(5):  # Try for 0.5 seconds
                    if process.poll() is not None:
                        break  # Process terminated
                    time.sleep(0.1)
                
                # If still running, force kill
                if process.poll() is None:
                    os.killpg(pgid, signal.SIGKILL)
                    
                # Wait for process to be fully killed
                process.wait(timeout=1)
                
            except (subprocess.TimeoutExpired, ProcessLookupError, PermissionError) as e:
                logger.warning(f"Error while killing process group {pgid}: {str(e)}")
                # Last resort: try to kill just the main process
                try:
                    process.kill()
                    process.wait(timeout=1)
                except Exception as e2:
                    logger.error(f"Failed to kill process: {str(e2)}")
            
            elapsed = time.time() - start_time
            stdout, stderr = "", "Timeout"
            retcode = -1
            
        # Create config_id
        config_id = f"{config.engine}"
        if config.template:
            config_id += f"_{config.template}"
        if config.aux_inv:
            config_id += "_aux"
        if "--prop-strengthen" in config.additional_opts:
            config_id += "_strengthen"
        
        # Special handling for ef engine
        if config.engine == "ef" and stdout:
            if "safe" in stdout.lower():
                retcode = 0  # Success
            elif "timeout" in stdout.lower():
                retcode = -1  # Timeout
            else:
                retcode = 1  # Failed]

        if config.engine == "kind" and stdout:
            if "unsafe" in stdout.lower() or "safe" in stdout.lower():
                retcode = 0  # Success
            elif "timeout" in stdout.lower():
                retcode = -1  # Timeout
            else:
                retcode = 1  # Failed
        
        return (input_file, config_id, retcode, stdout, stderr, elapsed)
        
    except Exception as e:
        elapsed = time.time() - start_time
        logger.error(f"Error running solver: {str(e)}")
        return input_file, config_id, 1, "", str(e), elapsed



def summarize_results(results: List[tuple]):
    logger = logging.getLogger('efmc_verifier')
    
    # Group results by configuration
    config_results = {}
    for result in results:
        file, config_id, retcode, stdout, stderr, elapsed = result
        
        if config_id not in config_results:
            config_results[config_id] = {
                'total': 0,
                'success': 0,
                'timeout': 0,
                'failed': 0,
                'total_time': 0.0,
                'max_time': 0.0,
                'files_success': [],
                'files_timeout': [],
                'files_failed': []
            }
        
        stats = config_results[config_id]
        stats['total'] += 1
        stats['total_time'] += elapsed
        stats['max_time'] = max(stats['max_time'], elapsed)
        
        if retcode == 0:
            stats['success'] += 1
            stats['files_success'].append(os.path.basename(file))
        elif retcode == -1:
            stats['timeout'] += 1
            stats['files_timeout'].append(os.path.basename(file))
        else:
            stats['failed'] += 1
            stats['files_failed'].append(os.path.basename(file))
    
    # Print summary
    print("\n=== Summary of Results ===")
    for config_id, stats in config_results.items():
        print(f"\nConfiguration: {config_id}")
        print(f"Total files processed: {stats['total']}")
        print(f"Successful verifications: {stats['success']} ({stats['success']*100/stats['total']:.1f}%)")
        print(f"Timeouts: {stats['timeout']} ({stats['timeout']*100/stats['total']:.1f}%)")
        print(f"Failed runs: {stats['failed']} ({stats['failed']*100/stats['total']:.1f}%)")
        print(f"Total time: {stats['total_time']:.2f}s")
        print(f"Average time: {stats['total_time']/stats['total']:.2f}s")
        print(f"Max time: {stats['max_time']:.2f}s")
        
        if stats['files_timeout']:
            print("\nTimeout files:")
            for f in sorted(stats['files_timeout']):
                print(f"  - {f}")
        
        if stats['files_failed']:
            print("\nFailed files:")
            for f in sorted(stats['files_failed']):
                print(f"  - {f}")

def main():
    parser = argparse.ArgumentParser(description="Run solver with multiple configurations")
    parser.add_argument("--bench-dir", required=True, help="Directory containing benchmark files")
    parser.add_argument("--timeout", type=int, required=True, help="Timeout in seconds")
    parser.add_argument("--config", help="Configuration file in JSON format")
    parser.add_argument("--parallel", action="store_true",
                        help="Run configurations in parallel")
    parser.add_argument("--solver", default="efmc",
                        help="Path to the solver executable")
    parser.add_argument("--log-level", default="INFO", 
                        choices=["DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"],
                        help="Set the logging level")
    args = parser.parse_args()
    
    # Setup logging
    log_level = getattr(logging, args.log_level)
    logger = setup_logging(log_level)
    
    logger.info(f"Starting EFMC verifier with bench-dir={args.bench_dir}, timeout={args.timeout}s")
    
    # Default configurations if no config file is provided
    configs = {
        "default": [
            # SolverConfig("pdr", aux_inv=False, lang="chc"),
            SolverConfig("ef", template="bv_interval",
                         aux_inv=False, lang="chc"
                         ),
            SolverConfig("kind", aux_inv=False, lang="chc"),
            SolverConfig("ef", template="bv_interval",
                         aux_inv=False, lang="chc",
                         additional_opts=["--prop-strengthen"]
                         )
        ]
    }

    if args.config:
        logger.info(f"Loading custom configuration from {args.config}")
        configs = load_config(args.config)
    else:
        logger.info("Using default configurations")

    # Check if benchmark directory exists
    if not os.path.isdir(args.bench_dir):
        logger.error(f"Benchmark directory does not exist: {args.bench_dir}")
        sys.exit(1)
        
    benchmark_files = [
        os.path.join(args.bench_dir, f)
        for f in os.listdir(args.bench_dir)
        if f.endswith((".sl", ".smt2"))
    ]
    
    logger.info(f"Found {len(benchmark_files)} benchmark files")
    
    if not benchmark_files:
        logger.warning(f"No .sl or .smt2 files found in {args.bench_dir}")
        sys.exit(1)
        
    results = []

    if args.parallel:
        logger.info("Running in parallel mode")
        with concurrent.futures.ProcessPoolExecutor() as executor:
            futures = []
            for config_name, config_list in configs.items():
                for config in config_list:
                    for benchmark in benchmark_files:
                        logger.debug(f"Submitting job: {os.path.basename(benchmark)} with engine {config.engine}")
                        futures.append(
                            executor.submit(
                                run_solver,
                                args.solver,
                                config,
                                benchmark,
                                args.timeout
                            )
                        )

            for future in concurrent.futures.as_completed(futures):
                result = future.result()
                results.append(result)
                # Print individual result immediately
                file, engine, retcode, stdout, stderr, elapsed = result
                print(f"\nFile: {os.path.basename(file)}")
                print(f"Engine: {engine}")
                print(f"Return code: {retcode}")
                print(f"Elapsed time: {elapsed:.2f}s")
                if stdout:
                    print("Output:")
                    print(stdout)
                if stderr:
                    print("Errors:")
                    print(stderr)
                sys.stdout.flush()
    else:
        logger.info("Running in sequential mode")
        for config_name, config_list in configs.items():
            for config in config_list:
                for benchmark in benchmark_files:
                    logger.debug(f"Processing: {os.path.basename(benchmark)} with engine {config.engine}")
                    result = run_solver(
                        args.solver,
                        config,
                        benchmark,
                        args.timeout
                    )
                    results.append(result)
                    # Print result immediately after processing each file
                    file, engine, retcode, stdout, stderr, elapsed = result
                    print(f"\nFile: {os.path.basename(file)}")
                    print(f"Engine: {engine}")
                    print(f"Return code: {retcode}")
                    print(f"Elapsed time: {elapsed:.2f}s")
                    if stdout:
                        print("Output:")
                        print(stdout)
                    if stderr:
                        print("Errors:")
                        print(stderr)
                    sys.stdout.flush()  # Ensure output is displayed immediately

    # Print final summary only
    print("\n" + "="*80)
    print("FINAL SUMMARY")
    print("="*80)
    logger.info(f"Completed {len(results)} verification tasks")
    summarize_results(results)
    sys.stdout.flush()


if __name__ == "__main__":
    main()

