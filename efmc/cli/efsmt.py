"""Command-line interface for EFSMT (Exists-Forall SMT) solver

python -m efmc.cli.efsmt --file query.smt2 --solver z3 --logic BV
"""

import argparse
import logging
import sys
import time
import signal
from multiprocessing import Pool, Manager, cpu_count
from io import StringIO

from efmc.engines.ef.efsmt.efsmt_solver import EFSMTSolver
from efmc.engines.ef.efsmt.efsmt_parser import EFSMTParser, ParserError

# pySMT imports for parallel solver
try:
    from pysmt.shortcuts import And, Bool, Not, Solver, Symbol, get_model, NotEquals
    from pysmt.smtlib.parser import SmtLibParser
    from pysmt.typing import BVType
    from pysmt.logics import QF_BV
    from pysmt.exceptions import SolverReturnedUnknownResultError
    PYSMT_AVAILABLE = True
except ImportError:
    PYSMT_AVAILABLE = False

logger = logging.getLogger(__name__)


class ParallelEFBVSolver:
    """Parallel EFBV solver using pySMT and multiprocessing"""
    
    def __init__(self, pool_size=cpu_count(), maxloops=50000, timeout=30):
        if not PYSMT_AVAILABLE:
            raise ImportError("pySMT is required for parallel solving")
        
        self.maxloops = maxloops
        self.pool = Pool(pool_size)
        self.timeout = timeout
        self.parser = EFSMTParser()
        
        # Synchronization
        manager = Manager()
        self.loops_lock = manager.Lock()
        self.e_phi_lock = manager.Lock()
        self.terminate_flag = manager.Value('b', False)
        self.e_phi = manager.list([Bool(True)])
        self.loops = manager.Value('i', 0)
        self.result = manager.dict()

    def _convert_z3_to_pysmt(self, z3_expr):
        """Convert Z3 expression to pySMT format"""
        smt2_str = z3_expr.sexpr()
        parser = SmtLibParser()
        script = parser.get_script(StringIO(smt2_str))
        return script.get_last_formula()

    def solve(self, phi_str, forall_vars):
        """Solve exists-forall formula using parallel approach"""
        # Parse with EFSMTParser
        self.parser.set_logic('BV')
        z3_exists_vars, z3_forall_vars, z3_formula = self.parser.parse_smt2_string(phi_str)
        
        # Convert to pySMT
        formula = self._convert_z3_to_pysmt(z3_formula)
        forall_vars_pysmt = [self._convert_z3_to_pysmt(v) for v in z3_forall_vars]
        
        start_time = time.time()
        
        while not self.terminate_flag.value:
            if self.timeout and time.time() - start_time > self.timeout:
                self.pool.terminate()
                raise SolverReturnedUnknownResultError("Timeout")
                
            with self.loops_lock:
                if self.loops.value >= self.maxloops:
                    self.pool.terminate()
                    raise SolverReturnedUnknownResultError("Maximum iterations reached")
            
            # Spawn worker process
            self.pool.apply_async(self._worker_process, 
                                args=(formula, forall_vars_pysmt),
                                callback=self._result_callback)
            
            time.sleep(0.01)
            
            if self.result:
                self.pool.terminate()
                return dict(self.result) if self.result else False

    def _worker_process(self, formula, forall_vars):
        """Worker process for parallel solving"""
        if self.terminate_flag.value:
            return None
            
        exists_vars = formula.get_free_variables() - set(forall_vars)
        
        with self.loops_lock:
            self.loops.value += 1
            
        try:
            with Solver(logic=QF_BV, name='z3') as esolver:
                with self.e_phi_lock:
                    for constraint in self.e_phi:
                        esolver.add_assertion(constraint)
                
                if esolver.solve():
                    tau = {v: esolver.get_value(v) for v in exists_vars}
                    sub_phi = formula.substitute(tau).simplify()
                    
                    fmodel = get_model(Not(sub_phi), logic=QF_BV, solver_name='z3')
                    if fmodel is None:
                        self.terminate_flag.value = True
                        return tau
                    else:
                        sigma = {v: fmodel[v] for v in forall_vars}
                        new_constraint = formula.substitute(sigma).simplify()
                        with self.e_phi_lock:
                            self.e_phi.append(new_constraint)
                else:
                    return False
        except Exception as e:
            logger.error(f"Worker process error: {e}")
            return None

    def _result_callback(self, result):
        """Callback for worker process results"""
        if result is True or (isinstance(result, dict) and result):
            self.terminate_flag.value = True
            self.result.update(result if isinstance(result, dict) else {})
        elif result is False:
            self.terminate_flag.value = True


class EFSMTRunner:
    """Main runner class for EFSMT solving tasks"""

    def __init__(self):
        self.logger = logging.getLogger(__name__)
        self.parser = EFSMTParser()

    def solve_efsmt_file(self, file_name: str, solver_name: str, logic: str = "BV",
                         parallel: bool = False, timeout: int = 30,
                         dump_smt2: bool = False, dump_qbf: bool = False, dump_cnf: bool = False):
        """Solve the EFSMT problem from a file"""
        try:
            start_time = time.time()
            self.parser.set_logic(logic)
            exists_vars, forall_vars, fml = self.parser.parse_smt2_file(file_name)

            # Handle parallel solving for BV logic
            if parallel and logic == "BV" and PYSMT_AVAILABLE:
                self.logger.info("Using parallel solver")
                with open(file_name, 'r') as f:
                    phi_str = f.read()
                
                parallel_solver = ParallelEFBVSolver(timeout=timeout)
                result = parallel_solver.solve(phi_str, forall_vars)
                
                if result:
                    print(f"Result: sat")
                    print(f"Model: {result}")
                else:
                    print(f"Result: unsat")
                print(f"Time: {time.time() - start_time:.2f}s")
                return

            # Use standard EFSMTSolver
            ef_solver = EFSMTSolver(logic=logic, solver=solver_name)
            ef_solver.init(exist_vars=exists_vars, forall_vars=forall_vars, phi=fml)

            # Handle dump requests
            if dump_smt2:
                out_file = f"{file_name}.efsmt2"
                ef_solver.dump_ef_smt_file(out_file)
                self.logger.info(f"Dumped SMT2 formula to {out_file}")
                return

            if dump_qbf:
                out_file = f"{file_name}.qdimacs"
                ef_solver.dump_qbf_file(out_file)
                self.logger.info(f"Dumped QBF formula to {out_file}")
                return

            if dump_cnf:
                out_file = f"{file_name}.cnf"
                ef_solver.dump_cnf_file(out_file)
                self.logger.info(f"Dumped CNF formula to {out_file}")
                return

            # Solve
            result = ef_solver.solve()
            print(f"Result: {result}")
            print(f"Time: {time.time() - start_time:.2f}s")

        except ParserError as e:
            self.logger.error(f"Parser error: {str(e)}")
            return str(e)
        except Exception as e:
            self.logger.error(f"Error solving EFSMT: {str(e)}")
            return str(e)


def parse_arguments():
    """Parse command line arguments"""
    parser = argparse.ArgumentParser(
        description='EFSMT - Exists-Forall SMT Solver',
        formatter_class=argparse.RawTextHelpFormatter
    )

    # Input options
    parser.add_argument('--file', type=str, required=True,
                        help='Input SMT2 file to solve')
    parser.add_argument('--logic', type=str, default='BV',
                        choices=['BV', 'UFBV', 'LIA', 'LRA', 'NIA', 'NRA', 'FP'],
                        help='Logic to use for solving')

    # Solver options
    parser.add_argument('solver', type=str, default='z3',
                        choices=['z3api', 'z3', 'cvc5', 'btor', 'yices2', 'mathsat', 'bitwuzla'],
                        help='SMT solver to use')
    
    # Parallel solving
    parser.add_argument('--parallel', action='store_true', default=False,
                        help='Use parallel solving (BV logic only, requires pySMT)')
    parser.add_argument('--timeout', type=int, default=30,
                        help='Timeout in seconds')

    # Output options
    parser.add_argument('--dump-smt2', action='store_true', default=False,
                        help='Dump the EFSMT query in SMT2 format')
    parser.add_argument('--dump-qbf', action='store_true', default=False,
                        help='Dump the EFSMT query in QBF format')
    parser.add_argument('--dump-cnf', action='store_true', default=False,
                        help='Dump the bit-blasted formula in CNF format')
    parser.add_argument('--verbose', action='store_true', default=False,
                        help='Enable verbose logging')

    return parser.parse_args()


def signal_handler(sig, frame):
    """Handle Ctrl+C gracefully"""
    print("\nTerminating...")
    sys.exit(0)


def main():
    """Main entry point"""
    signal.signal(signal.SIGINT, signal_handler)
    
    args = parse_arguments()

    if args.verbose:
        logging.basicConfig(level=logging.DEBUG)

    if args.parallel and not PYSMT_AVAILABLE:
        print("Warning: pySMT not available, falling back to sequential solving")
        args.parallel = False

    runner = EFSMTRunner()
    runner.solve_efsmt_file(
        file_name=args.file,
        solver_name=args.solver,
        logic=args.logic,
        parallel=args.parallel,
        timeout=args.timeout,
        dump_smt2=args.dump_smt2,
        dump_qbf=args.dump_qbf,
        dump_cnf=args.dump_cnf
    )


if __name__ == "__main__":
    sys.exit(main())
