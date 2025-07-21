"""
For calling SMT and QBF solvers

The available APIs:
- solve_with_bin_qbf: solve QBF via bin QBF solvers
- solve_with_bin_smt: solve SMT via bin SMT solvers
- solve_with_bin_smt_v2: solve SMT via bin SMT solvers (v2)
"""

import os
import time
import subprocess
import logging
import uuid
from typing import List
from threading import Timer

import z3

from efmc.smttools.smtlib_solver import SMTLIBSolver
from efmc.efmc_config import \
    z3_exec, cvc5_exec, g_bin_solver_timeout, caqe_exec, \
    btor_exec, bitwuzla_exec, yices_exec, math_exec, q3b_exec

logger = logging.getLogger(__name__)


def terminate(process, is_timeout: List):
    """Terminates a process and sets the timeout flag to True."""
    if process.poll() is None:
        try:
            process.terminate()
            # Wait briefly for graceful termination
            for _ in range(10):
                if process.poll() is not None:
                    break
                time.sleep(0.1)
            # Force kill if still running
            if process.poll() is None:
                process.kill()
            is_timeout[0] = True
        except Exception as ex:
            logger.error("Error while interrupting process: %s", str(ex))
            try:
                process.kill()
            except Exception:
                pass
            is_timeout[0] = True


def _run_solver_with_timeout(cmd, timeout=g_bin_solver_timeout):
    """Run solver command with timeout and return output."""
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    is_timeout = [False]
    timer = Timer(timeout, terminate, args=[p, is_timeout])
    timer.start()
    
    out = p.stdout.readlines()
    out = ' '.join([element.decode('UTF-8') for element in out])
    p.stdout.close()
    timer.cancel()
    
    if p.poll() is None:
        p.terminate()
    
    return out, is_timeout[0]


def solve_with_bin_qbf(fml_str: str, solver_name: str):
    """Call bin QBF solvers"""
    print(f"Solving QBF via {solver_name}")
    tmp_filename = f"/tmp/{uuid.uuid1()}_temp.qdimacs"
    
    try:
        with open(tmp_filename, "w") as tmp:
            tmp.write(fml_str)
        
        cmd = [caqe_exec, tmp_filename]  # Default to caqe for all QBF solvers
        out, is_timeout = _run_solver_with_timeout(cmd)
        
        print(out)
        if is_timeout:
            return "unknown"
        if "unsatisfiable" in out:
            return "unsat"
        elif "satisfiable" in out:
            return "sat"
        else:
            return "unknown"
    finally:
        if os.path.isfile(tmp_filename):
            os.remove(tmp_filename)


def solve_with_bin_smt(logic: str, x: List[z3.ExprRef], y: List[z3.ExprRef], phi: z3.ExprRef, solver_name: str):
    """Call bin SMT solvers to solve exists forall"""
    logger.debug(f"Solving EFSMT(BV) via {solver_name}")
    
    # Build SMT-LIB formula
    fml_str = f"(set-logic {logic})\n"
    
    # Declare exists variables (remove duplicates)
    exits_vars_names = set()
    for v in x:
        name = str(v)
        if name not in exits_vars_names:
            exits_vars_names.add(name)
            fml_str += f"(declare-const {v.sexpr()} {v.sort().sexpr()})\n"
    
    # Build quantified formula
    quant_vars = "(" + " ".join(f"({v.sexpr()} {v.sort().sexpr()})" for v in y) + ")\n"
    quant_fml_body = "(and \n" + "\n".join(f"  {fml.sexpr()}" for fml in phi.children()) + ")"
    fml_str += f"(assert (forall {quant_vars} {quant_fml_body}))\n(check-sat)\n"
    
    # Get solver command
    solver_cmds = {
        "z3": [z3_exec],
        "cvc5": [cvc5_exec, "-q", "--produce-models"],
        "btor": [btor_exec],
        "boolector": [btor_exec],
        "yices2": [yices_exec],
        "mathsat": [math_exec],
        "bitwuzla": [bitwuzla_exec],
        "q3b": [q3b_exec]
    }
    cmd = solver_cmds.get(solver_name, [z3_exec])
    
    tmp_filename = f"/tmp/{uuid.uuid1()}_temp.smt2"
    
    try:
        with open(tmp_filename, "w") as tmp:
            tmp.write(fml_str)
        
        cmd.append(tmp_filename)
        out, is_timeout = _run_solver_with_timeout(cmd)
        
        if is_timeout:
            return "unknown"
        elif "unsat" in out:
            return "unsat"
        elif "sat" in out:
            return "sat"
        else:
            return "unknown"
    finally:
        if os.path.isfile(tmp_filename):
            os.remove(tmp_filename)


def solve_with_bin_smt_v2(logic: str, y, phi: z3.ExprRef, solver_name: str):
    """Call bin SMT solvers using SMTLIBSolver (string-based communication)"""
    smt2string = f"(set-logic {logic})\n"
    sol = z3.Solver()
    sol.add(z3.ForAll(y, phi))
    smt2string += sol.to_smt2()
    
    # Get solver command
    solver_cmds = {
        "z3": z3_exec,
        "cvc5": f"{cvc5_exec} -q --produce-models"
    }
    bin_cmd = solver_cmds.get(solver_name, z3_exec)
    
    bin_solver = SMTLIBSolver(bin_cmd)
    start = time.time()
    res = bin_solver.check_sat_from_scratch(smt2string)
    
    if res == "sat":
        print("External solver success time: ", time.time() - start)
    elif res == "unsat":
        print("External solver fails time: ", time.time() - start)
    else:
        print("Seems timeout or error in the external solver")
        print(res)
    
    bin_solver.stop()
    return res


if __name__ == "__main__":
    # Demo functionality
    cmd = [cvc5_exec, "-q", "--produce-models", 'tmp.smt2']
    out, is_timeout = _run_solver_with_timeout(cmd)
    print(out)
