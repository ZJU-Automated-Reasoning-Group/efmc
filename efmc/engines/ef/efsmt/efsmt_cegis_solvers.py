from typing import List
import logging
import z3
from efmc.smttools.pysmt_solver import PySMTSolver

logger = logging.getLogger(__name__)


def simple_cegis_efsmt(logic: str, x: List[z3.ExprRef], y: List[z3.ExprRef], phi: z3.ExprRef, maxloops=None,
                       profiling=False , pysmt_solver="z3"):
    """
    A function to solve EFSMT using the CEGIS algorithm
    :param logic: The logic to use for solving
    :param x: The list of existential variables
    :param y: The list of universal variables
    :param phi: The z3 formula to solve
    :param maxloops: The maximum number of loops to run
    :param profiling: Whether to enable profiling or not
    :return: The solution
    """
    from pysmt.logics import QF_BV, QF_LIA, QF_LRA, AUTO
    if "IA" in logic:
        qf_logic = QF_LIA
    elif "RA" in logic:
        qf_logic = QF_LRA
    elif "BV" in logic:
        qf_logic = QF_BV
    else:
        qf_logic = AUTO
    sol = PySMTSolver()
    return sol.efsmt(evars=x, uvars=y, z3fml=phi,
                     logic=qf_logic, maxloops=maxloops,
                     esolver_name=pysmt_solver, fsolver_name=pysmt_solver)


"""
def simple_cegis_efsmt(logic: str, x: List[z3.ExprRef], y: List[z3.ExprRef], phi: z3.ExprRef, maxloops=None,
                       profiling=False):
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

    esolver.add(z3.BoolVal(True))

    loops = 0
    res = z3.unknown
    while maxloops is None or loops <= maxloops:
        loops += 1
        # print("round: ", loops)
        eres = esolver.check()
        if eres == z3.unsat:
            res = z3.unsat
            break
        else:
            emodel = esolver.model()
            mappings = [(var, emodel.eval(var, model_completion=True)) for var in x]
            sub_phi = z3.simplify(z3.substitute(phi, mappings))
            fsolver.push()
            fsolver.add(z3.Not(sub_phi))

            if fsolver.check() == z3.sat:
                fmodel = fsolver.model()
                y_mappings = [(var, fmodel.eval(var, model_completion=True)) for var in y]
                sub_phi = z3.simplify(z3.substitute(phi, y_mappings))
                esolver.add(sub_phi)
                fsolver.pop()
            else:
                res = z3.sat
                break
    return res
"""