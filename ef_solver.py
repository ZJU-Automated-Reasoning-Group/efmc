"""
Standalone tool for solving EFSMT queries
E.g. we can dump the queries from the template-based verification engine
"""

import sys
import psutil
import signal
import os
from typing import List
import subprocess
from threading import Timer
import logging
import z3

"""
模版方法的引擎实验
.smt2文件，.qdimacs (QBF), dimacs(CNF)
xxx.smt2+interval+yy+.smt2
xxx.smt2+interval+yyy+.qdiamcs
xxx.sy+interval+xxx+.smt2
....

对比不同模版，对比其他验证工具 (z3 py API)
"""

""""
3.to各种BOOL

- QBF: 需要找几个引擎 @孙家辉
- BDD： Q3B
- SAT: 我要完善实现
"""

from efmc.engines.ef.efsmt.efsmt_config import \
    z3_exec, cvc5_exec, g_bin_solver_timeout, caqe_exec, g_efsmt_args

logger = logging.getLogger(__name__)

def terminate(process, is_timeout: List):
    if process.poll() is None:
        try:
            process.terminate()
            is_timeout[0] = True
        except Exception as ex:
            print("error for interrupting")
            print(ex)

def solve_with_bin_qbf(file_name: str, solver_name: str):
    """Call bin QBF solvers
    """
    logger.debug("Solving QBF via {}".format(solver_name))
    try:
        if solver_name == "caqe":
            cmd = [caqe_exec, file_name]
        else:
            cmd = [caqe_exec, file_name]
        print(cmd)
        p_gene = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        is_timeout_gene = [False]
        timer_gene = Timer(g_bin_solver_timeout, terminate, args=[p_gene, is_timeout_gene])
        timer_gene.start()
        out_gene = p_gene.stdout.readlines()
        out_gene = ' '.join([str(element.decode('UTF-8')) for element in out_gene])
        p_gene.stdout.close()  # close?
        timer_gene.cancel()
        if p_gene.poll() is None:
            p_gene.terminate()  # TODO: need this?

        print(out_gene)
        if is_timeout_gene[0]:
            return "unknown"
        if "unsatisfiable" in out_gene:
            return "unsat"
        elif "satisfiable" in out_gene:
            return "sat"
        else:
            return "unknown"
    except Exception as ex:
        print("error for interrupting")
        print(ex)
        return "unknown"

def solve_with_bin_smt(file_name: str, solver_name: str):
    """Call bin SMT solvers to solve exists forall
    In this version, we create a temp file, and ...
    """
    logger.debug("Solving EFSMT(BV) via {}".format(solver_name))
    try:
        if solver_name == "z3":
            cmd = [z3_exec, file_name]
        elif solver_name == "cvc5":
            cmd = [cvc5_exec, "-q", "--produce-models", file_name]
        else:
            cmd = [z3_exec, file_name]
        p_gene = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        is_timeout_gene = [False]
        timer_gene = Timer(g_bin_solver_timeout, terminate, args=[p_gene, is_timeout_gene])
        timer_gene.start()
        out_gene = p_gene.stdout.readlines()
        out_gene = ' '.join([str(element.decode('UTF-8')) for element in out_gene])
        p_gene.stdout.close()  # close?
        timer_gene.cancel()
        if p_gene.poll() is None:
            p_gene.terminate()  # TODO: need this?

        if is_timeout_gene[0]:
            return "unknown"
        elif "unsat" in out_gene:
            return "unsat"
        elif "sat" in out_gene:
            return "sat"
        else:
            return "unknown"
    except Exception as ex:
        print("error for interrupting")
        print(ex)
        return "unknown"


def simple_cegis_efsmt(logic: str, x: List[z3.ExprRef], y: List[z3.ExprRef], phi: z3.ExprRef, maxloops=None, profiling=False):
    """ Solves exists x. forall y. phi(x, y) with simple CEGIS
    TODO: parse a quantified formula, exact x (existential vars), y (universal vars), and phi (the
      quantifier-free part) automatically.
    """
    # x = [item for item in get_vars(phi) if item not in y]
    # set_param("verbose", 15); set_param("smt.arith.solver", 3)
    if "IA" in logic:
        qf_logic = "QF_LIA"
    elif "RA" in logic:
        qf_logic = "QF_LRA"
    elif "BV" in logic:
        qf_logic = "QF_BV"
    else:
        qf_logic = ""

    if qf_logic != "":
        esolver = z3.SolverFor(qf_logic)
        fsolver = z3.SolverFor(qf_logic)
    else:
        esolver = z3.Solver()
        fsolver = z3.Solver()

    e_solver_cnts = []  # storing all the queries for profiling
    f_solver_cnts = []  # storing all the queries for profiling
    if profiling:
        e_solver_cnts.append("(set-logic {})".format(qf_logic))
        f_solver_cnts.append("(set-logic {})".format(qf_logic))
        for var in x:
            e_solver_cnts.append("(declare-const {0} {1})".format(var.sexpr(), var.sort().sexpr()))
        for var in y:
            f_solver_cnts.append("(declare-const {0} {1})".format(var.sexpr(), var.sort().sexpr()))

    esolver.add(z3.BoolVal(True))

    loops = 0
    res = z3.unknown
    while maxloops is None or loops <= maxloops:
        loops += 1
        # print("round: ", loops)
        eres = esolver.check()

        if profiling and loops >= 2:
            e_solver_cnts.append("(check-sat)")

        if eres == z3.unsat:
            res = z3.unsat
            break
        else:
            emodel = esolver.model()
            mappings = [(var, emodel.eval(var, model_completion=True)) for var in x]
            sub_phi = z3.simplify(z3.substitute(phi, mappings))
            fsolver.push()
            fsolver.add(z3.Not(sub_phi))

            if profiling:
                f_solver_cnts.append("(push)")
                f_solver_cnts.append("(assert {})".format(z3.Not(sub_phi).sexpr()))
                f_solver_cnts.append("(check-sat)")

            if fsolver.check() == z3.sat:
                fmodel = fsolver.model()
                y_mappings = [(var, fmodel.eval(var, model_completion=True)) for var in y]
                sub_phi = z3.simplify(z3.substitute(phi, y_mappings))
                esolver.add(sub_phi)
                fsolver.pop()
                if profiling:
                    e_solver_cnts.append("(assert {})".format(sub_phi.sexpr()))
                    f_solver_cnts.append("(pop)")
            else:
                res = z3.sat
                break
    if profiling:
        print(e_solver_cnts)
        print(f_solver_cnts)
    return res


def signal_handler(sig, frame):
    """The signal_handler function handles signals sent to the process.
    """
    print("handling signals")
    parent = psutil.Process(os.getpid())
    for child in parent.children(recursive=True):
        child.kill()
    sys.exit(0)


def demo_efsmt():
    import time
    x, y, z = z3.BitVecs("x y z", 16)
    # x, y, z = z3.Reals("x y z")
    fmla = z3.Implies(z3.And(y > 0, y < 10), y - 2 * x < 7)

    start = time.time()
    simple_cegis_efsmt("BV", [x], [y], fmla, profiling=True)
    print("time: ", time.time() - start)


if __name__ == "__main__":
    global g_efsmt_args
    import argparse

    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGQUIT, signal_handler)
    signal.signal(signal.SIGABRT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)

    demo_efsmt()
    exit(0)

    parser = argparse.ArgumentParser(formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument('--file', dest='file', default='none', type=str, help="Path to the input file")
    parser.add_argument('--smt-solver', dest='smt_solver', default='z3', type=str,
                        help="SMT solver (TODO: allow the user to specify a path to the solver?)")
    parser.add_argument('--qbf-solver', dest='qbf_solver', default='caqe', type=str,
                        help="QBF solver (TODO: allow the user to specify a path to the solver?)")
    parser.add_argument('--lang', dest='lang', default='smt2', type=str, help="The input format: smt2 or qbf")
    parser.add_argument('--timeout', dest='timeout', default=8, type=int, help="timeout")
    g_efsmt_args = parser.parse_args()

