# coding: utf-8
"""
A uniformed interface for solving Exists-ForAll problems
TODO: we should use the implementation in the pdsmt library (to reduce re-engineering..)
"""
import logging
import time
from typing import List

import z3
from z3.z3util import get_vars

from efmc.smttools.smt_exceptions import SmtlibError

g_has_smtib_support = True
try:
    from efmc.smttools.smtlib_solver import SMTLIBSolver
except Exception:
    # e.g., windows does not have fcntl
    g_has_smtib_support = False

logger = logging.getLogger(__name__)


def solve_efsmt_with_cegar(logic: str, y: List[z3.ExprRef], phi: z3.ExprRef, maxloops=None):
    """
    CEGAR-based EFSMT Solving
    :param logic: the type of the logic
    :param y: the universal quantified formula
    :param phi: the quantifier free part of the formula
    :param maxloops: maximum number of iterations
    :return: (z3.sat, emodel) or (z3.unsat, False) or (z3.unknown, False)
    """
    x = [item for item in get_vars(phi) if item not in y]
    if "RA" in logic:
        # LRA, UFLRA
        qf_logic = "QF_LRA"
    elif "BV" in logic:
        # BV, UFBV
        qf_logic = "QF_BV"
    elif "IA" in logic:
        # LIA, UFLIA
        qf_logic = "QF_LIA"
    else:
        qf_logic = "ALL"

    esolver = z3.SolverFor(qf_logic)
    fsolver = z3.SolverFor(qf_logic)
    esolver.add(z3.BoolVal(True))
    loops = 0
    while maxloops is None or loops <= maxloops:
        loops += 1
        if esolver.check() == z3.unsat:
            return z3.unsat, False
        else:
            emodel = esolver.model()
            mappings = [(var, emodel.eval(var, model_completion=True)) for var in x]
            # emodel yields a candidate invariant. can we build better sub_phi?...
            sub_phi = z3.simplify(z3.substitute(phi, mappings))
            fsolver.push()
            fsolver.add(z3.Not(sub_phi))
            if fsolver.check() == z3.sat:
                # the fmodel could be a counterexample of inductiveness (or init and post)
                # so, it would be interesting to better understand and utilize fmodel, e.g., by analyzing sub_phi?
                fmodel = fsolver.model()
                y_mappings = [(var, fmodel.eval(var, model_completion=True)) for var in y]
                sub_phi = z3.simplify(z3.substitute(phi, y_mappings))
                esolver.add(sub_phi)
                # esolver.add(z3.Tactic("solve-eqs")(sub_phi).as_expr())
                fsolver.pop()
            else:
                return z3.sat, emodel

    return z3.unknown, False


class EFSMTSolver:
    """Solving exists forall problem"""

    def __init__(self, logic: str):
        self.tactic = None
        self.logic = logic

    def solve_with_cegar(self, y: List[z3.ExprRef], phi: z3.ExprRef):
        """
        Solve with a CEGAR-style algorithm, which consists of a "forall solver" and an "exists solver"
        :return:
        """
        """This can be slow (perhaps not a good idea for NRA) Maybe good for LRA or BV?"""
        print("User-defined EFSMT starting!!!")
        z3_res, model = solve_efsmt_with_cegar(self.logic, y, phi)
        return z3_res, model

    def solve_with_bin_smt(self, y, phi: z3.ExprRef):
        """
        Build a quantified formula and send it to a third-party SMT solver
        that can handle quantified formulas
        :param y: the universal quantified variables
        :param phi: the quantifier-free part of the VC
        :return: TBD
        """
        if not g_has_smtib_support:
            raise SmtlibError("smtlib not supported (e.g., windows)s")

        smt2string = "(set-logic {})\n".format(self.logic)
        sol = z3.Solver()
        sol.add(z3.ForAll(y, phi))
        smt2string += sol.to_smt2()

        bin_cmd = f"/.../cvc5 -q --produce-models"
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
