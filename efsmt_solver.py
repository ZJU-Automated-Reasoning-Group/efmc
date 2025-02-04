"""
Standalone tool for solving EFSMT queries
E.g. we can dump the queries from the template-based verification engine
FIXME: we should support all the solvers in efmc/engines/efj/efsmt/efsmt_solver.py

Example usage:
    python efsmt_solver.py --file query.smt2 --smt-oracle z3 --timeout 30
"""
import logging
import time
import z3

from efmc.smttools.pysmt_solver import PySMTSolver
from efmc.utils import big_and
from efmc.utils.z3_expr_utils import get_variables

# from efmc.engines.ef.efsmt.efsmt_config import \
#    z3_exec, cvc5_exec, g_bin_solver_timeout, caqe_exec, g_efsmt_args

logger = logging.getLogger(__name__)


class EFSMTSolverError(Exception):
    """Base exception for EFSMT solver errors."""
    pass


def ground_quantifier(qexpr: z3.QuantifierRef):
    """
    Seems this can only handle exists x . fml, or forall x.fml?
    FIXME: it seems that this can be very slow?
    """
    try:
        body = qexpr.body()
        forall_vars = list()
        for i in range(qexpr.num_vars()):
            vi_name = qexpr.var_name(i)
            vi_sort = qexpr.var_sort(i)
            vi = z3.Const(vi_name, vi_sort)
            forall_vars.append(vi)

        # Substitute the free variables in body with the expression in var_list.
        body = z3.substitute_vars(body, *forall_vars)
        exists_vars = [x for x in get_variables(body) if x not in forall_vars]
        return exists_vars, forall_vars, body
    except Exception as e:
        raise EFSMTSolverError(f"Failed to ground quantifier: {str(e)}")


def demo_efsmt():
    x, y, z = z3.BitVecs("x y z", 16)
    fmla = z3.Implies(z3.And(y > 0, y < 10), y - 2 * x < 7)
    # print(ground_quantifier(z3.ForAll(y, fmla)))
    start = time.time()
    sol = PySMTSolver()
    print(sol.efsmt(evars=[x], uvars=[y], z3fml=fmla,
                    esolver_name="z3", fsolver_name="z3"))
    print("time: ", time.time() - start)


def solve_efsmt_file(file_name: str, smt_oracle: str):
    """
    Solve the EFSMT problem given a file name and an SMT oracle.
     Parameters:
    file_name (str): The name of the file containing the SMT2 formula.
    smt_oracle (str): The name of the SMT oracle to use.
     Returns:
    sol (PySMTSolver): The solution to the EFSMT problem.
    """

    # Start the timer.
    start = time.time()
    try:
        # Parse the SMT2 file into a Z3 formula.
        fml = big_and(z3.parse_smt2_file(file_name))
        # Ground the quantifiers in the formula.
        exists_vars, forall_vars, qf_fml = ground_quantifier(fml)
        # Create a PySMTSolver object
        sol = PySMTSolver()
        res = sol.efsmt(evars=exists_vars, uvars=forall_vars, z3fml=qf_fml,
                        esolver_name=smt_oracle, fsolver_name=smt_oracle)
        print(res)
        print("time: ", time.time() - start)
    except Exception as e:
        return str(e)


def main():
    import argparse

    parser = argparse.ArgumentParser(formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument('--file', dest='file', default='none', type=str, help="Path to the input file")
    parser.add_argument('--smt-oracle', dest='smt_oracle', default='z3', type=str,
                        help="Specify the SMT engine used by PySMT")
    parser.add_argument('--timeout', dest='timeout', default=8, type=int, help="timeout")
    parser.add_argument('--verbose', action='store_true',
                        help="Enable verbose logging")
    args = parser.parse_args()
    if args.verbose:
        logging.basicConfig(level=logging.DEBUG)

    solve_efsmt_file(args.file, args.smt_oracle)


if __name__ == "__main__":
    exit(main())
