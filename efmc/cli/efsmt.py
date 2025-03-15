"""Command-line interface for EFSMT (Exists-Forall SMT) solver

python -m efmc.cli.efsmt --file query.smt2 --solver z3 --logic BV
"""

import argparse
import logging
import sys
import time
import z3

from efmc.utils import big_and
from efmc.utils.z3_expr_utils import get_variables
from efmc.engines.ef.efsmt.efsmt_solver import EFSMTSolver
from efmc.engines.ef.efsmt.efsmt_parser import EFSMTParser, ParserError

logger = logging.getLogger(__name__)


class EFSMTRunner:
    """Main runner class for EFSMT solving tasks"""

    def __init__(self):
        self.logger = logging.getLogger(__name__)
        self.parser = EFSMTParser()

    def solve_efsmt_file(self, file_name: str, solver_name: str, logic: str = "BV",
                         dump_smt2: bool = False, dump_qbf: bool = False, dump_cnf: bool = False):
        """
        Solve the EFSMT problem from a file
        """
        try:
            # Parse the SMT2 file using EFSMTParser
            start_time = time.time()
            self.parser.set_logic(logic)
            exists_vars, forall_vars, fml = self.parser.parse_smt2_file(file_name)

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
    input_group = parser.add_argument_group('Input options')
    input_group.add_argument('--file', type=str, required=True,
                             help='Input SMT2 file to solve')
    input_group.add_argument('--logic', type=str, default='BV',
                             choices=['BV', 'UFBV', 'LIA', 'LRA', 'NIA', 'NRA'],
                             help='Logic to use for solving')

    # Solver options
    solver_group = parser.add_argument_group('EFSMT Solver options')

    # 1. QI-based
    solver_group.add_argument('solver', type=str, default='z3',
                              choices=['z3api', 'z3', 'cvc5', 'btor', 'yices2', 'mathsat', 'bitwuzla'],
                              help='SMT solver to use for direct solving (via quantifier instantiation)')
    # "z3api": use Z3's Python API (other choices will all binary solvers)

    # 2. Bit-level (bit-blasting?)
    solver_group.add_argument('--qbf-solver', type=str, default='z3qbf',
                              choices=['z3qbf', 'caqe', 'q3b'],
                              help='QBF solver to use after translation to QBF')
    solver_group.add_argument('--sat-solver', type=str, default='z3sat',
                              choices=['z3sat', 'cd', 'cd15', 'gc3', 'gc4', 'g3', 'g4', 'lgl',
                                       'mcb', 'mpl', 'mg3', 'mc', 'm22', 'mgh'],
                              help='SAT solver to use after translation to SAT')

    # 3. CEGIS-based
    solver_group.add_argument('--cegis', action='store_true', default=False,
                              help='Use CEGIS-based solving approach（implemented in pysmt')
    solver_group.add_argument('--cegis-solver', type=str, default='pysmt-z3',
                              choices=['pysmt-z3', 'pysmt-cvc5', 'pysmt-btor',
                                       'pysmt-yices2', 'pysmt-mathsat', 'pysmt-bitwuzla'],
                              help='Set SMT oracle used by the CEGIS-based algorithm (via pysmt)')

    solver_group.add_argument('--timeout', type=int, default=5,
                              help='Timeout in seconds (0 means no timeout)')

    # Output options
    output_group = parser.add_argument_group('Output options')
    output_group.add_argument('--dump-smt2', action='store_true', default=False,
                              help='Dump the EFSMT query in SMT2 format')
    output_group.add_argument('--dump-qbf', action='store_true', default=False,
                              help='Dump the EFSMT query in QBF format')
    output_group.add_argument('--dump-cnf', action='store_true', default=False,
                              help='Dump the bit-blasted formula in CNF format')
    output_group.add_argument('--output-dir', type=str, default='~/tmp',
                              help='Directory to store dumped files')
    output_group.add_argument('--verbose', action='store_true', default=False,
                              help='Enable verbose logging')
    output_group.add_argument('--stats', action='store_true', default=False,
                              help='Print solving statistics')

    # Advanced options
    advanced_group = parser.add_argument_group('Advanced options')
    advanced_group.add_argument('--simplify', action='store_true', default=False,
                                help='Apply formula simplification before solving')
    advanced_group.add_argument('--rewrite-exists', action='store_true', default=False,
                                help='Rewrite existential quantifiers using Skolemization')
    advanced_group.add_argument('--incremental', action='store_true', default=False,
                                help='Use incremental solving when possible')

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
