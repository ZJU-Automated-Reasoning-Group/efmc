#!/usr/bin/env python3
"""
Regression testing and profiling script for EFMC engines

# Run with default configurations
python regression.py data/BV --workers 4

# Run with custom engine configurations
python regression.py data/BV --workers 4 --config engine_config.json --output results.json

Example engine configuration file (engine_config.json):
[
  {
    "name": "ef",
    "template": "power_bv_interval",
    "signedness": "unsigned",
    "timeout": 300
  },
  {
    "name": "pdr",
    "timeout": 300
  },
  {
    "name": "kind",
    "aux_inv": true,
    "timeout": 300
  }
]
"""

import argparse
import concurrent.futures
import json
import logging
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional

from efmc.cli.efmc import EFMCRunner
from efmc.efmc_config import g_verifier_args, update_config_from_globals

logger = logging.getLogger(__name__)

@dataclass
class EngineConfig:
    name: str
    template: Optional[str] = None
    aux_inv: bool = False
    signedness: str = "unsigned"
    timeout: int = 300
    additional_args: Dict = None

    def to_dict(self):
        return {
            "name": self.name,
            "template": self.template,
            "aux_inv": self.aux_inv,
            "signedness": self.signedness,
            "timeout": self.timeout,
            "additional_args": self.additional_args or {}
        }

@dataclass
class BenchmarkResult:
    benchmark: str
    engine: str
    status: str
    time: float
    memory: float
    template: Optional[str] = None

class RegressionRunner:
    def __init__(self, benchmark_dir: str, workers: int = 1):
        self.benchmark_dir = Path(benchmark_dir)
        self.workers = workers
        self.results: List[BenchmarkResult] = []
        
        # Default engine configurations
        self.configs = [
            EngineConfig("pdr"),
            EngineConfig("ef", template="power_bv_interval"),
            EngineConfig("ef", template="bv_affine"),
            EngineConfig("kind", aux_inv=True),
            EngineConfig("qe")
        ]

    def load_config(self, config_file: str):
        """Load engine configurations from JSON file"""
        with open(config_file) as f:
            data = json.load(f)
            self.configs = [EngineConfig(**cfg) for cfg in data]

    def get_benchmarks(self) -> List[Path]:
        """Get all benchmark files recursively"""
        benchmarks = []
        for ext in [".sl", ".smt2"]:
            benchmarks.extend(self.benchmark_dir.rglob(f"*{ext}"))
        return sorted(benchmarks)

    def run_single_benchmark(self, benchmark: Path, config: EngineConfig) -> BenchmarkResult:
        """Run a single benchmark with given engine configuration"""
        start_time = time.time()
        
        # Configure verifier arguments
        g_verifier_args.engine = config.name
        g_verifier_args.template = config.template
        g_verifier_args.aux_inv = config.aux_inv
        g_verifier_args.signedness = config.signedness
        
        if config.additional_args:
            for k, v in config.additional_args.items():
                setattr(g_verifier_args, k, v)

        try:
            runner = EFMCRunner()
            if benchmark.suffix == ".sl":
                runner.verify_sygus(str(benchmark))
            else:
                runner.verify_chc(str(benchmark))
            
            elapsed = time.time() - start_time
            return BenchmarkResult(
                benchmark=str(benchmark),
                engine=config.name,
                status="completed",
                time=elapsed,
                memory=0.0,  # TODO: implement memory tracking
                template=config.template
            )
            
        except Exception as e:
            logger.error(f"Error running {benchmark} with {config.name}: {str(e)}")
            return BenchmarkResult(
                benchmark=str(benchmark),
                engine=config.name,
                status="error",
                time=0.0,
                memory=0.0,
                template=config.template
            )

    def run_all(self):
        """Run all benchmarks with all configurations"""
        benchmarks = self.get_benchmarks()
        total = len(benchmarks) * len(self.configs)
        logger.info(f"Running {total} tests ({len(benchmarks)} benchmarks × {len(self.configs)} configurations)")

        tasks = [(b, c) for b in benchmarks for c in self.configs]
        
        if self.workers > 1:
            with concurrent.futures.ProcessPoolExecutor(max_workers=self.workers) as executor:
                futures = [
                    executor.submit(self.run_single_benchmark, b, c)
                    for b, c in tasks
                ]
                for future in concurrent.futures.as_completed(futures):
                    self.results.append(future.result())
        else:
            for benchmark, config in tasks:
                result = self.run_single_benchmark(benchmark, config)
                self.results.append(result)

    def save_results(self, output_file: str):
        """Save results to JSON file"""
        results_dict = {
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "benchmark_dir": str(self.benchmark_dir),
            "configs": [c.to_dict() for c in self.configs],
            "results": [vars(r) for r in self.results]
        }
        
        with open(output_file, 'w') as f:
            json.dump(results_dict, f, indent=2)

def main():
    parser = argparse.ArgumentParser(description="EFMC Regression Testing")
    parser.add_argument("benchmark_dir", help="Directory containing benchmark files")
    parser.add_argument("--workers", type=int, default=1, help="Number of parallel workers")
    parser.add_argument("--config", help="JSON configuration file for engines")
    parser.add_argument("--output", default="regression_results.json", help="Output file for results")
    parser.add_argument("--verbose", action="store_true", help="Enable verbose logging")
    
    args = parser.parse_args()
    
    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format='%(asctime)s - %(levelname)s - %(message)s'
    )
    
    runner = RegressionRunner(args.benchmark_dir, args.workers)
    if args.config:
        runner.load_config(args.config)
    
    runner.run_all()
    runner.save_results(args.output)

if __name__ == "__main__":
    main()