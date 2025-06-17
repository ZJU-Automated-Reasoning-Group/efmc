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
from eval.eval_utils import kill_process_group, classify_result, detect_inconsistencies


def setup_logging(log_level=logging.INFO):
    logging.basicConfig(level=log_level, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
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
        cmd.extend(["--lang", self.lang, *self.additional_opts])
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
        name: [VerifierConfig(**c) for c in cfg]
        for name, cfg in data.items()
    }


def run_verifier(verifier_path: str, config: VerifierConfig, input_file: str, timeout: int) -> tuple:
    start_time = time.time()
    cmd = [verifier_path] + config.get_command_args() + ["--file", input_file]
    
    try:
        process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, 
                                 text=True, preexec_fn=os.setsid)
        pgid = os.getpgid(process.pid)
        
        try:
            stdout, stderr = process.communicate(timeout=timeout)
            retcode = process.returncode
        except subprocess.TimeoutExpired:
            kill_process_group(process, pgid, logging.getLogger('efmc_verifier'))
            stdout, stderr = "", "Timeout"
            retcode = -1
        
        elapsed = time.time() - start_time
        result = classify_result(config, retcode, stdout)
        return (input_file, config.config_id, result, stdout, stderr, elapsed)
        
    except Exception as e:
        elapsed = time.time() - start_time
        logging.getLogger('efmc_verifier').error(f"Error running verifier: {e}")
        return input_file, config.config_id, "unknown", "", str(e), elapsed


def print_result(result):
    file, engine, result_class, stdout, stderr, elapsed = result
    print(f"\nFile: {os.path.basename(file)}, Engine: {engine}, Result: {result_class}, Time: {elapsed:.2f}s")
    if stdout:
        print(f"Output: {stdout}")
    if stderr:
        print(f"Errors: {stderr}")
    sys.stdout.flush()


def summarize_results(results: List[tuple]):
    config_results = {}
    
    # Collect statistics
    for file, config_id, result_class, stdout, stderr, elapsed in results:
        if config_id not in config_results:
            config_results[config_id] = {
                'total': 0, 'safe': 0, 'unsafe': 0, 'timeout': 0, 'unknown': 0,
                'total_time': 0.0, 'max_time': 0.0
            }
        
        stats = config_results[config_id]
        stats['total'] += 1
        stats['total_time'] += elapsed
        stats['max_time'] = max(stats['max_time'], elapsed)
        stats[result_class] += 1
    
    # Print comparison table
    print("\n=== Configuration Comparison Table ===")
    if config_results:
        print(f"{'Configuration':<25} {'Total':<6} {'Safe':<6} {'Unsafe':<7} {'Solved':<7} {'Timeout':<8} {'Unknown':<8} {'Success%':<10} {'Avg Time':<10} {'Max Time':<10}")
        print("-" * 110)
        
        # Sort by solved rate (safe + unsafe)
        sorted_configs = sorted(config_results.items(), 
                              key=lambda x: (x[1]['safe'] + x[1]['unsafe']) / x[1]['total'], 
                              reverse=True)
        
        for config_id, stats in sorted_configs:
            total = stats['total']
            total_solved = stats['safe'] + stats['unsafe']  # All definitive results
            success_rate = total_solved * 100 / total
            avg_time = stats['total_time'] / total
            
            print(f"{config_id:<25} {total:<6} {stats['safe']:<6} {stats['unsafe']:<7} {total_solved:<7} "
                  f"{stats['timeout']:<8} {stats['unknown']:<8} {success_rate:<9.1f}% "
                  f"{avg_time:<9.2f}s {stats['max_time']:<9.2f}s")
    
    # Print inconsistency report
    inconsistencies = detect_inconsistencies(results)
    if inconsistencies:
        print(f"\n=== INCONSISTENT RESULTS DETECTED ({len(inconsistencies)} files) ===")
        print("WARNING: Conflicting verification results detected!\n")
        
        for filename, file_data in sorted(inconsistencies.items()):
            print(f"File: {filename}")
            
            # Group by result type
            by_result = {}
            for data in file_data:
                result = data['result']
                by_result.setdefault(result, []).append(data)
            
            # Show conflicting definitive results
            for result_type, configs in by_result.items():
                if result_type in ['safe', 'unsafe']:
                    config_names = [c['config'] for c in configs]
                    print(f"  {result_type.upper()}: {', '.join(config_names)}")
            
            print("  All results:")
            for data in sorted(file_data, key=lambda x: x['config']):
                print(f"    {data['config']}: {data['result']} ({data['elapsed']:.2f}s)")
            print()
        
        print(f"Total inconsistent files: {len(inconsistencies)}\n")
    else:
        print("\n=== NO INCONSISTENCIES DETECTED ===")


def run_all_configs(configs, benchmark_files, args, parallel=False):
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
                VerifierConfig("ef", template="bv_octagon", aux_inv=False, lang="chc"),
                VerifierConfig("ef", template="knownbits", aux_inv=False, lang="chc"),
                VerifierConfig("ef", template="knownbits", aux_inv=False, lang="chc", additional_opts=["--prop-strengthen"]),
                #VerifierConfig("ef", template="bitpredabs", aux_inv=False, lang="chc", additional_opts=["--prop-strengthen"]),
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
    
    # Run all configurations and summarize
    results = run_all_configs(configs, benchmark_files, args, args.parallel)
    
    print("\n" + "="*80)
    print("FINAL SUMMARY")
    print("="*80)
    logger.info(f"Completed {len(results)} verification tasks")
    
    inconsistencies = detect_inconsistencies(results)
    if inconsistencies:
        logger.warning(f"DETECTED {len(inconsistencies)} FILES WITH INCONSISTENT RESULTS!")
    
    summarize_results(results)


if __name__ == "__main__":
    main()

