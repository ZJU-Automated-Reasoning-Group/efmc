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


def signal_handler(sig, frame):
    """The signal_handler function handles signals sent to the process.
    """
    print("handling signals")
    parent = psutil.Process(os.getpid())
    for child in parent.children(recursive=True):
        child.kill()
    sys.exit(0)


def solve_smt2_file(filename, solver_name):
    return False


def solve_qbf_file(filename, solver_name):
    return False


if __name__ == "__main__":
    global g_efsmt_args
    import argparse

    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGQUIT, signal_handler)
    signal.signal(signal.SIGABRT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)

    parser = argparse.ArgumentParser(formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument('--file', dest='file', default='none', type=str, help="Path to the input file")
    parser.add_argument('--smt-solver', dest='smt_solver', default='z3', type=str,
                        help="SMT solver (TODO: allow the user to specify a path to the solver?)")
    parser.add_argument('--qbf-solver', dest='qbf_solver', default='caqe', type=str,
                        help="QBF solver (TODO: allow the user to specify a path to the solver?)")
    parser.add_argument('--lang', dest='lang', default='smt2', type=str, help="The input format: smt2 or qbf")
    parser.add_argument('--timeout', dest='timeout', default=8, type=int, help="timeout")
    g_efsmt_args = parser.parse_args()

    if g_efsmt_args .lang == "smt2":
        solve_smt2_file(g_efsmt_args .file, g_efsmt_args .smt_solver)
    elif g_efsmt_args .lang == "qbf":
        solve_qbf_file(g_efsmt_args .file, g_efsmt_args .qbf_solver)
    else:
        print("Not supported format {}".format(g_efsmt_args .lang))
        exit(0)
