"""
Standalone tool for solving EFSMT queries
E.g. we can dump the queries from the template-based verification engine
"""
import logging
import time
import z3

# from efmc.engines.ef.efsmt.efsmt_config import \
#    z3_exec, cvc5_exec, g_bin_solver_timeout, caqe_exec, g_efsmt_args

from efmc.smttools.pysmt_solver import PySMTSolver
from efmc.utils import big_and

logger = logging.getLogger(__name__)

def ground_quantifier(qexpr: z3.QuantifierRef):
    """
    Seems this can only handle exists x . fml, or forall x.fml?
    FIXME: it seems that this can be very slow?
    """
    from z3.z3util import get_vars
    # get_vars can be slow
    body = qexpr.body()
    forall_vars = list()
    for i in range(qexpr.num_vars()):
        vi_name = qexpr.var_name(i)
        vi_sort = qexpr.var_sort(i)
        vi = z3.Const(vi_name, vi_sort)
        forall_vars.append(vi)

    # Substitute the free variables in body with the expression in var_list.
    body = z3.substitute_vars(body, *forall_vars)
    exists_vars = [x for x in get_vars(body) if x not in forall_vars]
    return exists_vars, forall_vars, body


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
    """Solve the EFSMT file using CEGIS (implemented using PySMT)
    :param file_name: the quantified SMT instance
    :param smt_oracle: the SMT engine used by PySMT"""
    fml = big_and(z3.parse_smt2_file(file_name))
    exists_vars, forall_vars, qf_fml = ground_quantifier(fml)
    start = time.time()
    sol = PySMTSolver()
    print(sol.efsmt(evars=exists_vars, uvars=forall_vars, z3fml=qf_fml,
                    esolver_name=smt_oracle, fsolver_name=smt_oracle))

    print("time: ", time.time() - start)


if __name__ == "__main__":
    global g_efsmt_args
    import argparse

    # demo_efsmt()
    # solve_efsmt_file("/Users/rainoftime/Desktop/xx.smt2", "z3")
    # exit(0)

    parser = argparse.ArgumentParser(formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument('--file', dest='file', default='none', type=str, help="Path to the input file")
    parser.add_argument('--smt-oracle', dest='smt_oracle', default='z3', type=str,
                        help="Specify the SMT engine used by PySMT")
    # parser.add_argument('--timeout', dest='timeout', default=8, type=int, help="timeout")
    g_args = parser.parse_args()
    solve_efsmt_file(g_args.file, g_args.smt_oracle)
