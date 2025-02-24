"""Command-line interface for EFSMT (Exists-Forall SMT) solver

python -m efmc.cli.efsmt --file query.smt2 --solver z3 --logic BV
"""

import argparse
import logging
import sys
import time
import z3

from efmc.engines.ef.efsmt.efsmt_solver import EFSMTSolver
from efmc.utils import big_and
from efmc.utils.z3_expr_utils import get_variables

logger = logging.getLogger(__name__)

class EFSMTRunner:
    """Main runner class for EFSMT solving tasks"""
    
    def __init__(self):
        self.logger = logging.getLogger(__name__)

    def solve_efsmt_file(self, file_name: str, solver_name: str, logic: str = "BV", 
                        dump_smt2: bool = False, dump_qbf: bool = False):
        """
        Solve the EFSMT problem from a file
        """
        try:
            # Parse the SMT2 file
            start_time = time.time()
            fml = big_and(z3.parse_smt2_file(file_name))
            
            # Extract variables
            all_vars = get_variables(fml)
            exists_vars = []
            forall_vars = []
            
            # Initialize solver
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
            
            # Solve
            result = ef_solver.solve()
            print(f"Result: {result}")
            print(f"Time: {time.time() - start_time:.2f}s")
            
        except Exception as e:
            self.logger.error(f"Error solving EFSMT: {str(e)}")
            return str(e)

def parse_arguments():
    """Parse command line arguments"""
    parser = argparse.ArgumentParser(
        description='EFSMT - Exists-Forall SMT Solver',
        formatter_class=argparse.RawTextHelpFormatter
    )
    
    parser.add_argument('--file', type=str, required=True,
                      help='Input SMT2 file to solve')
    
    parser.add_argument('--solver', type=str, default='z3',
                      choices=['z3', 'cvc5', 'btor', 'yices2', 'mathsat', 'bitwuzla',
                              'z3qbf', 'caqe', 'q3b', 'z3sat', 'cegis',
                              'cd', 'cd15', 'gc3', 'gc4', 'g3', 'g4', 'lgl',
                              'mcb', 'mpl', 'mg3', 'mc', 'm22', 'mgh'],
                      help='SMT/QBF/SAT solver to use')
    
    parser.add_argument('--logic', type=str, default='BV',
                      choices=['BV', 'UFBV', 'LIA', 'LRA', 'NIA', 'NRA'],
                      help='Logic to use for solving')
    
    parser.add_argument('--dump-smt2', action='store_true',
                      help='Dump the EFSMT query in SMT2 format')
    
    parser.add_argument('--dump-qbf', action='store_true',
                      help='Dump the EFSMT query in QBF format')
    
    parser.add_argument('--verbose', action='store_true',
                      help='Enable verbose logging')
    
    return parser.parse_args()

def main():
    """Main entry point"""
    args = parse_arguments()
    
    if args.verbose:
        logging.basicConfig(level=logging.DEBUG)
    
    runner = EFSMTRunner()
    runner.solve_efsmt_file(
        file_name=args.file,
        solver_name=args.solver,
        logic=args.logic,
        dump_smt2=args.dump_smt2,
        dump_qbf=args.dump_qbf
    )

if __name__ == "__main__":
    sys.exit(main())