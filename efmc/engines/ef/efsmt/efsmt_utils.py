import os
import time
from typing import List
import subprocess
from threading import Timer
import logging

import z3

from efmc.smttools.smtlib_solver import SMTLIBSolver
from efmc.engines.ef.efsmt.efsmt_config import \
    z3_exec, cvc5_exec, g_bin_solver_timeout, caqe_exec

logger = logging.getLogger(__name__)


def terminate(process, is_timeout: List):
    """
        Terminates a process and sets the timeout flag to True.
        process : subprocess.Popen
            The process to be terminated.
        is_timeout : List
            A list containing a single boolean item. If the process exceeds the timeout limit, the boolean item will be
            set to True.
        """
    if process.poll() is None:
        try:
            process.terminate()
            is_timeout[0] = True
        except Exception as ex:
            print("error for interrupting")
            print(ex)


def solve_with_bin_qbf(fml_str: str, solver_name: str):
    """Call bin QBF solvers
    """
    logger.debug("Solving QBF via {}".format(solver_name))
    tmp = open("/tmp/temp.qdimacs", "w")
    tmp_filename = "/tmp/temp.qdimacs"
    try:
        tmp.write(fml_str)
        tmp.close()
        if solver_name == "caqe":
            cmd = [caqe_exec, tmp_filename]
        else:
            cmd = [caqe_exec, tmp_filename]
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

        os.remove(tmp_filename)  # rm the tmp file

        print(out_gene)
        if is_timeout_gene[0]:
            return "unknown"
        if "unsatisfiable" in out_gene:
            return "unsat"
        elif "satisfiable" in out_gene:
            return "sat"
        else:
            return "unknown"
    finally:
        tmp.close()
        if os.path.isfile(tmp_filename):
            os.remove(tmp_filename)


def solve_with_bin_smt(logic: str, y, phi: z3.ExprRef, solver_name: str):
    """Call bin SMT solvers to solve exists forall
    In this version, we create a temp file, and ...
    """
    logger.debug("Solving EFSMT(BV) via {}".format(solver_name))
    fml_str = "(set-logic {})\n".format(logic)
    sol = z3.Solver()
    sol.add(z3.ForAll(y, phi))
    fml_str += sol.to_smt2()
    tmp = open("/tmp/temp.smt2", "w")
    tmp_filename = "/tmp/temp.smt2"
    try:
        tmp.write(fml_str)
        tmp.close()
        if solver_name == "z3":
            cmd = [z3_exec, tmp_filename]
        elif solver_name == "cvc5":
            cmd = [cvc5_exec, "-q", "--produce-models", tmp_filename]
        else:
            cmd = [z3_exec, tmp_filename]
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

        os.remove(tmp_filename)  # rm the tmp file

        if is_timeout_gene[0]:
            return "unknown"
        elif "unsat" in out_gene:
            return "unsat"
        elif "sat" in out_gene:
            return "sat"
        else:
            return "unknown"
    finally:
        tmp.close()
        if os.path.isfile(tmp_filename):
            os.remove(tmp_filename)


def solve_with_bin_smt_v2(logic: str, y, phi: z3.ExprRef, solver_name: str):
    """Call bin SMT solvers to solve exists forall
    In thi version, I use the SMLIBSolver (We can send strings to the bin solver)
    """
    smt2string = "(set-logic {})\n".format(logic)
    sol = z3.Solver()
    sol.add(z3.ForAll(y, phi))
    smt2string += sol.to_smt2()

    # bin_cmd = ""
    if solver_name == "z3":
        bin_cmd = z3_exec
    elif solver_name == "cvc5":
        bin_cmd = cvc5_exec + " -q --produce-models"
    else:
        bin_cmd = z3_exec

    bin_solver = SMTLIBSolver(bin_cmd)
    start = time.time()
    res = bin_solver.check_sat_from_scratch(smt2string)
    if res == "sat":
        # print(bin_solver.get_expr_values(["p1", "p0", "p2"]))
        print("External solver success time: ", time.time() - start)
        # TODO: get the model to build the invariant
    elif res == "unsat":
        print("External solver fails time: ", time.time() - start)
    else:
        print("Seems timeout or error in the external solver")
        print(res)
    bin_solver.stop()
    return res


def demo_solver():
    cmd = [cvc5_exec, "-q", "--produce-models", '/Users/rainoftime/Work/efmc/efmc/tests/tmp.smt2']
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


if __name__ == "__main__":
    demo_solver()
