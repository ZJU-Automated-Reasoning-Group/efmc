"""
Use this script to test different engines in efmc

1. Where can the test cases come from:
- Use problems form a directory: CHC files  ("*.smt2") or SyGuS files ("*.sl"). Need to parse each file to get the corresponding transition system.
- Use problems randomly generated (the random generator is  efmc/tests/sts_generator.py):  

2. Allow for testing transition systems of different types (refer to the TransitionSystem class):
- Boolean programs
- Integer programs
- Real programs
- Bit-vector programs

3. Criteria of likely bugs (refer to the VerificationResult class):
- A returns "unsafe" and B returns "safe"
- A returns "safe" and B returns "unsafe"

4. TBD: different engines can support different types of transition systems. We need a way to configure this? 
"""

import os
import glob
import time
import argparse
import logging
import json
import pickle
from typing import List, Dict, Any, Optional, Tuple
from dataclasses import dataclass
import z3

from efmc.sts import TransitionSystem
from efmc.utils.verification_utils import VerificationResult
from efmc.tests.sts_generator import TransitionSystemGenerator
from efmc.frontends import parse_chc, parse_sygus

# Import all available engines
from efmc.engines.pdr.pdr_prover import PDRProver
from efmc.engines.kinduction.kind_prover import KInductionProver
from efmc.engines.bdd.bdd_prover import BDDProver
from efmc.engines.ef.ef_prover import EFProver
from efmc.engines.qi.qi_prover import QuantifierInstantiationProver
from efmc.engines.houdini.houdini_prover import HoudiniProver
from efmc.engines.abduction.abduction_prover import AbductionProver
from efmc.engines.predabs.predabs_prover import PredicateAbstractionProver
from efmc.engines.symabs.symabs_prover import SymbolicAbstractionProver

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler("difftest.log"),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger("difftest")

@dataclass
class EngineConfig:
    """Configuration for a verification engine"""
    name: str
    engine_class: type
    supported_types: List[str]
    k_value: int = None
    timeout: int = None
    additional_params: Dict[str, Any] = None

@dataclass
class TestResult:
    """Result of a test case"""
    test_name: str
    engine_name: str
    result: VerificationResult
    execution_time: float
    error: Optional[str] = None

class DiffTester:
    """Main class for differential testing of verification engines"""
    
    def __init__(self, config_file: Optional[str] = None):
        self.engines: Dict[str, EngineConfig] = {}
        self.test_results: List[TestResult] = []
        self.generator = TransitionSystemGenerator()
        self.systems_map: Dict[str, TransitionSystem] = {}  # Store systems by name
        
        # Register available engines with default configurations
        self._register_default_engines()
        
        # Load custom configuration if provided
        if config_file:
            self._load_config(config_file)
    
    def _register_default_engines(self):
        """Register all available engines with their default configurations"""
        self.engines = {
            "pdr": EngineConfig(
                name="PDR",
                engine_class=PDRProver,
                supported_types=["bool", "int", "real", "bv"],
                timeout=60  # Default timeout of 60 seconds
            ),
            "kind": EngineConfig(
                name="K-Induction",
                engine_class=KInductionProver,
                supported_types=["bool", "int", "real", "bv"],
                k_value=10  # Default k value for K-Induction
            ),
            "bdd": EngineConfig(
                name="BDD",
                engine_class=BDDProver,
                supported_types=["bool"]  # BDD works best with boolean programs
            ),
            "ef": EngineConfig(
                name="EF",
                engine_class=EFProver,
                supported_types=["bool", "int", "real", "bv"],
                additional_params={"template_type": "interval"}
            ),
            "qi": EngineConfig(
                name="QI",
                engine_class=QuantifierInstantiationProver,
                supported_types=["bool", "int", "real", "bv"]
            ),
            "houdini": EngineConfig(
                name="Houdini",
                engine_class=HoudiniProver,
                supported_types=["bool", "int", "real", "bv"]
            ),
            "abduction": EngineConfig(
                name="Abduction",
                engine_class=AbductionProver,
                supported_types=["bool", "int", "real"]
            ),
            "predabs": EngineConfig(
                name="Predicate Abstraction",
                engine_class=PredicateAbstractionProver,
                supported_types=["bool", "int", "real", "bv"]
            ),
            "symabs": EngineConfig(
                name="Symbolic Abstraction",
                engine_class=SymbolicAbstractionProver,
                supported_types=["bool", "bv"]
            )
        }
    
    def _load_config(self, config_file: str):
        """Load custom engine configurations from a JSON file"""
        try:
            with open(config_file, 'r') as f:
                config = json.load(f)
            
            # Update engine configurations
            for engine_name, engine_config in config.get("engines", {}).items():
                if engine_name in self.engines:
                    # Update existing engine configuration
                    for key, value in engine_config.items():
                        if key == "timeout":
                            self.engines[engine_name].timeout = value
                        elif key == "additional_params":
                            if self.engines[engine_name].additional_params is None:
                                self.engines[engine_name].additional_params = {}
                            self.engines[engine_name].additional_params.update(value)
                        elif key == "supported_types":
                            self.engines[engine_name].supported_types = value
                        elif key == "k_value":
                            self.engines[engine_name].k_value = value
                else:
                    logger.warning(f"Unknown engine: {engine_name}")
            
            logger.info(f"Loaded configuration from {config_file}")
        except Exception as e:
            logger.error(f"Failed to load configuration: {e}")
    
    def _get_system_type(self, system: TransitionSystem) -> str:
        """Determine the type of a transition system"""
        if system.has_bool:
            return "bool"
        elif system.has_int:
            return "int"
        elif system.has_real:
            return "real"
        elif system.has_bv:
            return "bv"
        else:
            return "unknown"
    
    def _is_engine_compatible(self, engine_config: EngineConfig, system_type: str) -> bool:
        """Check if an engine is compatible with a transition system type"""
        return system_type in engine_config.supported_types
    
    def _run_engine(self, engine_config: EngineConfig, system: TransitionSystem) -> Tuple[VerificationResult, float, Optional[str]]:
        """Run a verification engine on a transition system"""
        start_time = time.time()
        error = None
        result = None
        
        try:
            # Initialize engine with additional parameters if provided
            if engine_config.additional_params:
                engine = engine_config.engine_class(system, **engine_config.additional_params)
            else:
                engine = engine_config.engine_class(system)
            
            # Run the engine with timeout
            if engine_config.name == "K-Induction":
                # K-Induction requires a 'k' parameter, default to 10 if not specified
                k_value = engine_config.k_value if engine_config.k_value is not None else 10
                result = engine.solve(k=k_value)
            elif engine_config.name == "PDR" and engine_config.timeout is not None:
                result = engine.solve(timeout=engine_config.timeout)
            else:
                result = engine.solve()
        except Exception as e:
            error = str(e)
            logger.error(f"Error running {engine_config.name}: {e}")
        
        execution_time = time.time() - start_time
        
        # If execution took longer than timeout, mark as unknown
        if engine_config.timeout is not None and execution_time > engine_config.timeout:
            logger.warning(f"{engine_config.name} timed out after {execution_time:.2f} seconds")
            if result:
                result.is_unknown = True
            else:
                result = VerificationResult(False, None, None, True)
            error = f"Timeout after {execution_time:.2f} seconds"
        
        return result, execution_time, error
    
    def load_systems_from_directory(self, directory: str, file_type: str = "smt2") -> List[Tuple[str, TransitionSystem]]:
        """Load transition systems from files in a directory"""
        systems = []
        
        if file_type not in ["smt2", "sl"]:
            logger.error(f"Unsupported file type: {file_type}")
            return systems
        
        pattern = os.path.join(directory, f"*.{file_type}")
        files = glob.glob(pattern)
        
        for file_path in files:
            try:
                file_name = os.path.basename(file_path)
                logger.info(f"Loading {file_name}")
                
                if file_type == "smt2":
                    all_vars, init, trans, post = parse_chc(file_path, to_real_type=False)
                    system = TransitionSystem()
                    system.from_z3_cnts([all_vars, init, trans, post])
                else:  # file_type == "sl"
                    all_vars, init, trans, post = parse_sygus(file_path, to_real_type=False)
                    system = TransitionSystem()
                    system.from_z3_cnts([all_vars, init, trans, post])
                
                if system and system.initialized:
                    systems.append((file_name, system))
                else:
                    logger.warning(f"Failed to load valid transition system from {file_name}")
            except Exception as e:
                logger.error(f"Error loading {file_path}: {e}")
        
        logger.info(f"Loaded {len(systems)} transition systems from {directory}")
        return systems
    
    def generate_random_systems(self, count: int, types: List[str] = None) -> List[Tuple[str, TransitionSystem]]:
        """Generate random transition systems"""
        systems = []
        
        if types is None:
            types = ["bool", "int", "real", "bv"]
        
        for i in range(count):
            try:
                system_type = types[i % len(types)]
                
                if system_type == "bool":
                    system = self.generator.gen_bool_program()
                    name = f"random_bool_{i}"
                elif system_type == "int":
                    system = self.generator.gen_lia_program()
                    name = f"random_int_{i}"
                elif system_type == "real":
                    system = self.generator.gen_lra_program()
                    name = f"random_real_{i}"
                elif system_type == "bv":
                    system = self.generator.gen_bv_program()
                    name = f"random_bv_{i}"
                else:
                    continue
                
                systems.append((name, system))
            except Exception as e:
                logger.error(f"Error generating random system: {e}")
        
        logger.info(f"Generated {len(systems)} random transition systems")
        return systems
    
    def run_tests(self, systems: List[Tuple[str, TransitionSystem]], engines: List[str] = None):
        """Run tests on the given systems with the specified engines"""
        if engines is None:
            engines = list(self.engines.keys())
        
        for system_name, system in systems:
            # Store the system for potential later use
            self.systems_map[system_name] = system
            
            system_type = self._get_system_type(system)
            logger.info(f"Testing {system_name} (type: {system_type})")
            
            for engine_name in engines:
                if engine_name not in self.engines:
                    logger.warning(f"Unknown engine: {engine_name}")
                    continue
                
                engine_config = self.engines[engine_name]
                
                if not self._is_engine_compatible(engine_config, system_type):
                    logger.info(f"Skipping {engine_config.name} (incompatible with {system_type})")
                    continue
                
                logger.info(f"Running {engine_config.name} on {system_name}")
                result, execution_time, error = self._run_engine(engine_config, system)
                
                test_result = TestResult(
                    test_name=system_name,
                    engine_name=engine_config.name,
                    result=result,
                    execution_time=execution_time,
                    error=error
                )
                
                self.test_results.append(test_result)
                
                if result:
                    status = "safe" if result.is_safe else "unsafe"
                    if result.is_unknown:
                        status = "unknown"
                    logger.info(f"{engine_config.name} result: {status} (time: {execution_time:.2f}s)")
                else:
                    logger.warning(f"{engine_config.name} failed to produce a result")
    
    def analyze_results(self) -> List[Dict[str, Any]]:
        """Analyze test results to find potential bugs"""
        potential_bugs = []
        
        # Group results by test case
        test_cases = {}
        for result in self.test_results:
            if result.test_name not in test_cases:
                test_cases[result.test_name] = []
            test_cases[result.test_name].append(result)
        
        # Analyze each test case
        for test_name, results in test_cases.items():
            # Skip test cases with fewer than 2 results
            if len(results) < 2:
                continue
            
            # Check for disagreements
            safe_engines = []
            unsafe_engines = []
            unknown_engines = []
            
            for result in results:
                if result.error:
                    continue
                
                if result.result.is_unknown:
                    unknown_engines.append(result.engine_name)
                elif result.result.is_safe:
                    safe_engines.append(result.engine_name)
                else:
                    unsafe_engines.append(result.engine_name)
            
            # If we have both safe and unsafe results, this is a potential bug
            if safe_engines and unsafe_engines:
                bug = {
                    "test_name": test_name,
                    "safe_engines": safe_engines,
                    "unsafe_engines": unsafe_engines,
                    "unknown_engines": unknown_engines,
                    "severity": "high"
                }
                potential_bugs.append(bug)
                logger.warning(f"Potential bug in {test_name}: disagreement between engines")
                logger.warning(f"  Safe: {', '.join(safe_engines)}")
                logger.warning(f"  Unsafe: {', '.join(unsafe_engines)}")
                if unknown_engines:
                    logger.warning(f"  Unknown: {', '.join(unknown_engines)}")
        
        return potential_bugs
    
    def save_problematic_systems(self, output_dir: str):
        """Save transition systems that lead to potential bugs"""
        if not os.path.exists(output_dir):
            os.makedirs(output_dir)
            logger.info(f"Created directory: {output_dir}")
        
        # Get potential bugs
        potential_bugs = self.analyze_results()
        
        # Save each problematic system
        for bug in potential_bugs:
            test_name = bug["test_name"]
            if test_name in self.systems_map:
                system = self.systems_map[test_name]
                
                # Save as SMT2 for human readability and debugging
                smt2_path = os.path.join(output_dir, f"{test_name}.smt2")
                with open(smt2_path, 'w') as f:
                    f.write(system.to_smt2())
                
                # Save bug details in JSON format
                json_path = os.path.join(output_dir, f"{test_name}_details.json")
                with open(json_path, 'w') as f:
                    json.dump({
                        "test_name": test_name,
                        "safe_engines": bug["safe_engines"],
                        "unsafe_engines": bug["unsafe_engines"],
                        "unknown_engines": bug.get("unknown_engines", []),
                        "severity": bug["severity"]
                    }, f, indent=2)
                
                logger.info(f"Saved problematic system {test_name} to {smt2_path} and {json_path}")
        
        logger.info(f"Saved {len(potential_bugs)} problematic systems to {output_dir}")
    
    def generate_report(self, output_file: str = "difftest_report.json"):
        """Generate a report of test results"""
        report = {
            "summary": {
                "total_tests": len(set(r.test_name for r in self.test_results)),
                "total_engines": len(set(r.engine_name for r in self.test_results)),
                "total_results": len(self.test_results)
            },
            "results": [],
            "potential_bugs": self.analyze_results()
        }
        
        # Add detailed results
        for result in self.test_results:
            if result.result:
                status = "safe" if result.result.is_safe else "unsafe"
                if result.result.is_unknown:
                    status = "unknown"
                
                report["results"].append({
                    "test_name": result.test_name,
                    "engine_name": result.engine_name,
                    "status": status,
                    "execution_time": result.execution_time,
                    "error": result.error
                })
            else:
                report["results"].append({
                    "test_name": result.test_name,
                    "engine_name": result.engine_name,
                    "status": "error",
                    "execution_time": result.execution_time,
                    "error": result.error
                })
        
        # Write report to file
        with open(output_file, 'w') as f:
            json.dump(report, f, indent=2)
        
        logger.info(f"Report generated: {output_file}")
        
        # Print summary
        print("\nTest Summary:")
        print(f"Total test cases: {report['summary']['total_tests']}")
        print(f"Total engines: {report['summary']['total_engines']}")
        print(f"Total results: {report['summary']['total_results']}")
        print(f"Potential bugs: {len(report['potential_bugs'])}")
        
        if report['potential_bugs']:
            print("\nPotential Bugs:")
            for i, bug in enumerate(report['potential_bugs']):
                print(f"{i+1}. Test: {bug['test_name']}")
                print(f"   Safe engines: {', '.join(bug['safe_engines'])}")
                print(f"   Unsafe engines: {', '.join(bug['unsafe_engines'])}")
                if bug['unknown_engines']:
                    print(f"   Unknown engines: {', '.join(bug['unknown_engines'])}")
                print()

def main():
    parser = argparse.ArgumentParser(description="Differential testing for EFMC verification engines")
    
    # Input sources
    input_group = parser.add_mutually_exclusive_group(required=True)
    input_group.add_argument("--dir", help="Directory containing test files")
    input_group.add_argument("--random", type=int, help="Number of random test cases to generate")
    
    # File type for directory input
    parser.add_argument("--file-type", choices=["smt2", "sl"], default="smt2", 
                        help="File type for directory input (default: smt2)")
    
    # Engine selection
    parser.add_argument("--engines", nargs="+", help="Engines to test (default: all)")
    
    # System types for random generation
    parser.add_argument("--types", nargs="+", choices=["bool", "int", "real", "bv"], 
                        default=["bool", "int", "real", "bv"],
                        help="Types of systems to generate randomly (default: all)")
    
    # Configuration
    parser.add_argument("--config", help="Path to configuration file")
    
    # K-Induction specific
    parser.add_argument("--k-value", type=int, default=10,
                        help="K value for K-Induction (default: 10)")
    
    # Output
    parser.add_argument("--output", default="difftest_report.json", 
                        help="Output file for test report (default: difftest_report.json)")
    
    # Save problematic systems
    parser.add_argument("--save-bugs", help="Directory to save problematic transition systems")
    
    # Timeout
    # FIXME, in this file, we run the engines via the Python API, so the timeout maynot work (even we set timeout Z3 and set a few checkpoints in the high-level engines.) Thus, we'd better not to use "too complex" systems
    # or use engiens that are often too slow and hard to control the timout, e.g., PDR?
    parser.add_argument("--timeout", type=int, help="Timeout in seconds for engines that support it", default=60)
    
    args = parser.parse_args()
    
    # Initialize tester
    tester = DiffTester(args.config)
    
    # Update K value for K-Induction if specified
    if "kind" in tester.engines and args.k_value:
        tester.engines["kind"].k_value = args.k_value
    
    # Update timeout for PDR if specified
    if "pdr" in tester.engines and args.timeout:
        tester.engines["pdr"].timeout = args.timeout
    
    # Load or generate test systems
    systems = []
    if args.dir:
        systems = tester.load_systems_from_directory(args.dir, args.file_type)
    else:  # args.random
        systems = tester.generate_random_systems(args.random, args.types)
    
    if not systems:
        logger.error("No test systems available")
        return
    
    # Run tests
    tester.run_tests(systems, args.engines)
    
    # Generate report
    tester.generate_report(args.output)
    
    # Save problematic systems if requested
    if args.save_bugs:
        tester.save_problematic_systems(args.save_bugs)

if __name__ == "__main__":
    """
    An example command to cursor: use the random sts generator; compare kind and abduction provers; run 30 tests
    """
    main()
