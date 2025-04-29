"""
For verifying Lustre programs.. (not used for now..)
"""
import os
import subprocess
import sys
import glob
import time
import argparse
import logging
from datetime import datetime

# Setup logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler("jkind_runner.log"),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger("JKindRunner")

# Default configuration
EXPERIMENTS_DIR = 'benchmarks'
RESULTS_DIR = 'results'
TIMEOUT = 3600
SOLVERS = ['z3', 'yices', 'smtinterpol', 'mathsat']
ENGINES = [('k_ind', ['-pdr_max', '0']),
           ('pdr', ['-no_bmc', '-no_k_induction', '-no_inv_gen']),
           ('both', [])]

def parse_arguments():
    parser = argparse.ArgumentParser(description='Run JKind verification on Lustre programs')
    parser.add_argument('--benchmarks', default=EXPERIMENTS_DIR, help='Directory containing Lustre files')
    parser.add_argument('--results', default=RESULTS_DIR, help='Directory for storing results')
    parser.add_argument('--timeout', type=int, default=TIMEOUT, help='Timeout in seconds')
    parser.add_argument('--solvers', nargs='+', default=SOLVERS, help='SMT solvers to use')
    parser.add_argument('--debug', action='store_true', help='Enable debug output')
    return parser.parse_args()

def find_jkind_jar():
    """Find jkind.jar in the environment paths"""
    jkind_jar = None
    
    # Check JKIND_HOME first
    jkind_home = os.environ.get("JKIND_HOME")
    if jkind_home:
        jar_path = os.path.join(jkind_home, "jkind.jar")
        if os.path.exists(jar_path):
            return jar_path
    
    # Check PATH environment variable (use : as separator for macOS)
    path = os.environ.get("PATH", "")
    for directory in path.split(':'):
        jar_path = os.path.join(directory, "jkind.jar")
        if os.path.exists(jar_path):
            return jar_path
    
    return None

def run_single_jkind(solver, engine_args, xml_path, file_path, timeout):
    """Run JKind with specific solver and engine arguments"""
    start_time = time.time()
    
    args = ['java', '-jar', jkind_jar, '-jkind',
            '-support',
            '-timeout', str(timeout),
            '-n', '1000000',
            '-solver', solver,
            '-xml', xml_path,
            file_path] + engine_args
    
    log_file = os.path.join(os.path.dirname(xml_path), f"{os.path.basename(xml_path)}.log")
    
    logger.info(f"Running JKind: {' '.join(args)}")
    
    try:
        with open(log_file, "w") as log:
            proc = subprocess.Popen(
                args, 
                stdout=log, 
                stderr=subprocess.STDOUT,
                text=True
            )
            proc.wait(timeout=timeout + 10)  # Add a small buffer to the timeout
            
        elapsed = time.time() - start_time
        logger.info(f"Completed in {elapsed:.2f} seconds")
        return True
    except subprocess.TimeoutExpired:
        logger.warning(f"Process timed out after {timeout} seconds")
        proc.kill()
        return False
    except Exception as e:
        logger.error(f"Error running JKind: {str(e)}")
        return False

def run_all_jkind(lus_file, results_dir, experiments_dir, solvers, engines, timeout):
    """Run JKind with all solvers and engines for a single Lustre file"""
    result_dir = os.path.join(results_dir, os.path.splitext(lus_file)[0])
    os.makedirs(result_dir, exist_ok=True)
    
    lus_path = os.path.join(experiments_dir, lus_file)
    total_runs = len(engines) * len(solvers)
    completed = 0
    
    for engine_name, engine_args in engines:
        for solver in solvers:
            xml_file = f"{solver}_{engine_name}"
            xml_path = os.path.join(result_dir, xml_file)
            
            success = run_single_jkind(solver, engine_args, xml_path, lus_path, timeout)
            completed += 1
            
            # Print progress
            progress = completed / total_runs * 100
            sys.stdout.write(f"\rProgress: {progress:.1f}% ({completed}/{total_runs})")
            sys.stdout.flush()
    
    sys.stdout.write("\n")
    return result_dir

def main():
    args = parse_arguments()
    
    if args.debug:
        logger.setLevel(logging.DEBUG)
    
    global EXPERIMENTS_DIR, RESULTS_DIR, TIMEOUT, SOLVERS
    EXPERIMENTS_DIR = args.benchmarks
    RESULTS_DIR = args.results
    TIMEOUT = args.timeout
    SOLVERS = args.solvers
    
    # Add timestamp to results directory to prevent overwriting
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    RESULTS_DIR = f"{RESULTS_DIR}_{timestamp}"
    
    logger.info(f"Starting JKind verification")
    logger.info(f"Benchmarks directory: {EXPERIMENTS_DIR}")
    logger.info(f"Results directory: {RESULTS_DIR}")
    
    # Gather Lustre files
    if not os.path.exists(EXPERIMENTS_DIR):
        logger.error(f"'{EXPERIMENTS_DIR}' directory does not exist")
        sys.exit(-1)
    
    os.chdir(EXPERIMENTS_DIR)
    lus_files = glob.glob("*.lus")
    if len(lus_files) == 0:
        logger.error(f"No Lustre files found in '{EXPERIMENTS_DIR}' directory")
        sys.exit(-1)
    os.chdir("..")
    
    # Find jkind.jar
    global jkind_jar
    jkind_jar = find_jkind_jar()
    if jkind_jar is None:
        logger.error("Unable to find jkind.jar in JKIND_HOME or PATH environment variables")
        sys.exit(-1)
    logger.info(f"Using JKind: {jkind_jar}")
    
    # Create output directory
    os.makedirs(RESULTS_DIR, exist_ok=True)
    
    # Run JKind on all files
    start_time = time.time()
    results = {}
    
    for i, lus_file in enumerate(lus_files):
        logger.info(f"Processing ({i+1} of {len(lus_files)}) {lus_file}")
        result_dir = run_all_jkind(lus_file, RESULTS_DIR, EXPERIMENTS_DIR, SOLVERS, ENGINES, TIMEOUT)
        results[lus_file] = result_dir
    
    # Write summary
    total_time = time.time() - start_time
    logger.info(f"Completed all verifications in {total_time:.2f} seconds")
    
    with open(os.path.join(RESULTS_DIR, "summary.txt"), "w") as summary:
        summary.write(f"JKind Verification Summary\n")
        summary.write(f"========================\n")
        summary.write(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        summary.write(f"Total time: {total_time:.2f} seconds\n")
        summary.write(f"Files processed: {len(lus_files)}\n\n")
        
        for lus_file, result_dir in results.items():
            summary.write(f"{lus_file}: {result_dir}\n")
    
    logger.info(f"Results saved to {RESULTS_DIR}")

if __name__ == "__main__":
    main()
