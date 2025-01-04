#!/usr/bin/env python3
import argparse
import concurrent.futures
import json
import os
import subprocess
import sys
import time
from typing import List, Dict


class SolverConfig:
    def __init__(self, engine: str, template: str = None, aux_inv: bool = False,
                 lang: str = "sygus", additional_opts: List[str] = None):
        self.engine = engine
        self.template = template
        self.aux_inv = aux_inv
        self.lang = lang
        self.additional_opts = additional_opts or []

    def get_command_args(self) -> List[str]:
        cmd = ["efmc.py", "--engine", self.engine]
        if self.template:
            cmd.extend(["--template", self.template])
        cmd.extend(["--aux-inv", str(self.aux_inv).lower()])
        cmd.extend(["--lang", self.lang])
        cmd.extend(self.additional_opts)
        return cmd


def load_config(config_file: str) -> Dict[str, List[SolverConfig]]:
    with open(config_file) as f:
        data = json.load(f)

    configs = {}
    for name, cfg in data.items():
        configs[name] = [
            SolverConfig(
                engine=c.get("engine"),
                template=c.get("template"),
                aux_inv=c.get("aux_inv", False),
                lang=c.get("lang", "sygus"),
                additional_opts=c.get("additional_opts", [])
            ) for c in cfg
        ]
    return configs


def run_solver(solver_path: str, config: SolverConfig, input_file: str,
               timeout: int) -> tuple:
    start_time = time.time()
    cmd = [solver_path] + config.get_command_args() + ["--file", input_file]

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout
        )
        elapsed = time.time() - start_time
        return (input_file, config.engine, result.returncode,
                result.stdout, result.stderr, elapsed)
    except subprocess.TimeoutExpired:
        elapsed = time.time() - start_time
        return input_file, config.engine, -1, "", "Timeout", elapsed


def main():
    parser = argparse.ArgumentParser(description="Run solver with multiple configurations")
    parser.add_argument("benchmark_dir", help="Directory containing benchmark files")
    parser.add_argument("timeout", type=int, help="Timeout in seconds")
    parser.add_argument("--config", help="Configuration file in JSON format")
    parser.add_argument("--parallel", action="store_true",
                        help="Run configurations in parallel")
    parser.add_argument("--solver", default="./venv/bin/python3",
                        help="Path to the solver executable")
    args = parser.parse_args()

    # Default configurations if no config file is provided
    configs = {
        "default": [
            SolverConfig("pdr", aux_inv=False, lang="sygus"),
            SolverConfig("efsmt", template="power_bv_interval",
                         aux_inv=False, lang="chc")
        ]
    }

    if args.config:
        configs = load_config(args.config)

    benchmark_files = [
        os.path.join(args.benchmark_dir, f)
        for f in os.listdir(args.benchmark_dir)
        if f.endswith(".sl")
    ]

    results = []

    if args.parallel:
        with concurrent.futures.ProcessPoolExecutor() as executor:
            futures = []
            for config_name, config_list in configs.items():
                for config in config_list:
                    for benchmark in benchmark_files:
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
                results.append(future.result())
    else:
        for config_name, config_list in configs.items():
            for config in config_list:
                for benchmark in benchmark_files:
                    results.append(
                        run_solver(
                            args.solver,
                            config,
                            benchmark,
                            args.timeout
                        )
                    )

    # Print results
    for result in results:
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


if __name__ == "__main__":
    main()
