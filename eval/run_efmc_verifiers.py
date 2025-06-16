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


def setup_logging(log_level=logging.INFO):
    logging.basicConfig(
        level=log_level,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    )
    return logging.getLogger('efmc_verifier')


class VerifierConfig:
    def __init__(self, engine: str, template: str = None, aux_inv: bool = False, 
                 lang: str = "sygus", additional_opts: List[str] = None):
        self.engine = engine
        self.template = template
        self.aux_inv = aux_inv
        self.lang = lang
        self.additional_opts = additional_opts or []

    def get_command_args(self) -> List[str]:
        cmd = ["--engine", self.engine]
        if self.template:
            cmd.extend(["--template", self.template])
        if self.aux_inv:
            cmd.append("--kind-aux-inv")
        cmd.extend(["--lang", self.lang])
        cmd.extend(self.additional_opts)
        return cmd

    @property
    def config_id(self) -> str:
        config_id = self.engine
        if self.template:
            config_id += f"_{self.template}"
        if self.aux_inv:
            config_id += "_aux"
        if "--prop-strengthen" in self.additional_opts:
            config_id += "_strengthen"
        return config_id


def load_config(config_file: str) -> Dict[str, List[VerifierConfig]]:
    with open(config_file) as f:
        data = json.load(f)
    
    return {
        name: [
            VerifierConfig(
                engine=c.get("engine"),
                template=c.get("template"),
                aux_inv=c.get("aux_inv", False),
                lang=c.get("lang", "chc"),
                additional_opts=c.get("additional_opts", [])
            ) for c in cfg
        ] for name, cfg in data.items()
    }


def kill_process_group(process, pgid, logger):
    """Kill process group with graceful termination followed by force kill"""
    try:
        os.killpg(pgid, signal.SIGTERM)
        for _ in range(5):
            if process.poll() is not None:
                break
            time.sleep(0.1)
        if process.poll() is None:
            os.killpg(pgid, signal.SIGKILL)
        process.wait(timeout=1)
    except (subprocess.TimeoutExpired, ProcessLookupError, PermissionError) as e:
        logger.warning(f"Error killing process group {pgid}: {e}")
        try:
            process.kill()
            process.wait(timeout=1)
        except Exception as e2:
            logger.error(f"Failed to kill process: {e2}")


def normalize_retcode(config, stdout, retcode):
    """Normalize return codes based on engine-specific output patterns"""
    if not stdout:
        return retcode
    
    stdout_lower = stdout.lower()
    if config.engine == "ef":
        if "safe" in stdout_lower:
            return 0
        elif "timeout" in stdout_lower:
            return -1
        else:
            return 1
    elif config.engine == "kind":
        if "unsafe" in stdout_lower or "safe" in stdout_lower:
            return 0
        elif "timeout" in stdout_lower:
            return -1
        else:
            return 1
    return retcode


def run_verifier(verifier_path: str, config: VerifierConfig, input_file: str, timeout: int) -> tuple:
    start_time = time.time()
    cmd = [verifier_path] + config.get_command_args() + ["--file", input_file]
    
    try:
        process = subprocess.Popen(
            cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, 
            text=True, preexec_fn=os.setsid
        )
        pgid = os.getpgid(process.pid)
        
        try:
            stdout, stderr = process.communicate(timeout=timeout)
            retcode = process.returncode
        except subprocess.TimeoutExpired:
            kill_process_group(process, pgid, logging.getLogger('efmc_verifier'))
            stdout, stderr = "", "Timeout"
            retcode = -1
        
        elapsed = time.time() - start_time
        retcode = normalize_retcode(config, stdout, retcode)
        return (input_file, config.config_id, retcode, stdout, stderr, elapsed)
        
    except Exception as e:
        elapsed = time.time() - start_time
        logging.getLogger('efmc_verifier').error(f"Error running verifier: {e}")
        return input_file, config.config_id, 1, "", str(e), elapsed


def print_result(result):
    """Print individual result"""
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


def summarize_results(results: List[tuple]):
    config_results = {}
    
    for file, config_id, retcode, stdout, stderr, elapsed in results:
        if config_id not in config_results:
            config_results[config_id] = {
                'total': 0, 'success': 0, 'timeout': 0, 'failed': 0,
                'total_time': 0.0, 'max_time': 0.0, 'files_timeout': []
            }
        
        stats = config_results[config_id]
        stats['total'] += 1
        stats['total_time'] += elapsed
        stats['max_time'] = max(stats['max_time'], elapsed)
        
        if retcode == 0:
            stats['success'] += 1
        elif retcode == -1:
            stats['timeout'] += 1
            stats['files_timeout'].append(os.path.basename(file))
        else:
            stats['failed'] += 1
    
    """
    print("\n=== Summary of Results ===")
    for config_id, stats in config_results.items():
        total = stats['total']
        print(f"\nConfiguration: {config_id}")
        print(f"Total files: {total}")
        print(f"Success: {stats['success']} ({stats['success']*100/total:.1f}%)")
        print(f"Timeout: {stats['timeout']} ({stats['timeout']*100/total:.1f}%)")
        print(f"Failed: {stats['failed']} ({stats['failed']*100/total:.1f}%)")
        print(f"Total time: {stats['total_time']:.2f}s")
        print(f"Avg time: {stats['total_time']/total:.2f}s")
        print(f"Max time: {stats['max_time']:.2f}s")
        
        if stats['files_timeout']: # TODO: this info is useful for debugging
            print("Timeout files:")
            for f in sorted(stats['files_timeout']):
                print(f"  - {f}")
    """

    # Print comparison table
    print("\n=== Configuration Comparison Table ===")
    if config_results:
        # Header
        print(f"{'Configuration':<25} {'Total':<6} {'Success':<8} {'Timeout':<8} {'Failed':<7} {'Success%':<10} {'Avg Time':<10} {'Max Time':<10}")
        print("-" * 95)
        
        # Sort configurations by success rate (descending)
        sorted_configs = sorted(config_results.items(), 
                              key=lambda x: x[1]['success'] / x[1]['total'], 
                              reverse=True)
        
        for config_id, stats in sorted_configs:
            total = stats['total']
            success_rate = stats['success'] * 100 / total
            avg_time = stats['total_time'] / total
            
            print(f"{config_id:<25} {total:<6} {stats['success']:<8} {stats['timeout']:<8} {stats['failed']:<7} "
                  f"{success_rate:<9.1f}% {avg_time:<9.2f}s {stats['max_time']:<9.2f}s")


def run_all_configs(configs, benchmark_files, args, parallel=False):
    """Run all configurations on all benchmark files"""
    results = []
    
    if parallel:
        with concurrent.futures.ProcessPoolExecutor() as executor:
            futures = [
                executor.submit(run_verifier, args.verifier, config, benchmark, args.timeout)
                for config_list in configs.values()
                for config in config_list
                for benchmark in benchmark_files
            ]
            
            for future in concurrent.futures.as_completed(futures):
                result = future.result()
                results.append(result)
                print_result(result)
    else:
        for config_list in configs.values():
            for config in config_list:
                for benchmark in benchmark_files:
                    result = run_verifier(args.verifier, config, benchmark, args.timeout)
                    results.append(result)
                    print_result(result)
    
    return results


def main():
    parser = argparse.ArgumentParser(description="Run verifier with multiple configurations")
    parser.add_argument("--bench-dir", required=True, help="Directory containing benchmark files")
    parser.add_argument("--timeout", type=int, required=True, help="Timeout in seconds")
    parser.add_argument("--config", help="Configuration file in JSON format")
    parser.add_argument("--parallel", action="store_true", help="Run configurations in parallel")
    parser.add_argument("--verifier", default="efmc", help="Path to the verifier executable")
    parser.add_argument("--log-level", default="INFO", 
                        choices=["DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"],
                        help="Set the logging level")
    args = parser.parse_args()
    
    logger = setup_logging(getattr(logging, args.log_level))
    logger.info(f"Starting EFMC verifier with bench-dir={args.bench_dir}, timeout={args.timeout}s")
    
    # Load configurations
    if args.config:
        configs = load_config(args.config)
        logger.info(f"Loaded custom configuration from {args.config}")
    else:
        configs = {
            "default": [
                VerifierConfig("ef", template="bv_interval", aux_inv=False, lang="chc"),
                VerifierConfig("kind", aux_inv=False, lang="chc"),
                #VerifierConfig("ef", template="bv_zono", aux_inv=False, lang="chc"),
                VerifierConfig("ef", template="bv_octagon", aux_inv=False, lang="chc"),
                #VerifierConfig("pdr", lang="chc"),
                VerifierConfig("ef", template="bv_interval", aux_inv=False, lang="chc", additional_opts=["--prop-strengthen"])
            ]
        }
        logger.info("Using default configurations")
    
    # Get benchmark files
    if not os.path.isdir(args.bench_dir):
        logger.error(f"Benchmark directory does not exist: {args.bench_dir}")
        sys.exit(1)
        
    benchmark_files = [
        os.path.join(args.bench_dir, f)
        for f in os.listdir(args.bench_dir)
        if f.endswith((".sl", ".smt2"))
    ]
    
    if not benchmark_files:
        logger.warning(f"No .sl or .smt2 files found in {args.bench_dir}")
        sys.exit(1)
    
    logger.info(f"Found {len(benchmark_files)} benchmark files")
    
    # Run all configurations
    results = run_all_configs(configs, benchmark_files, args, args.parallel)
    
    # Print final summary
    print("\n" + "="*80)
    print("FINAL SUMMARY")
    print("="*80)
    logger.info(f"Completed {len(results)} verification tasks")
    summarize_results(results)


if __name__ == "__main__":
    main()

