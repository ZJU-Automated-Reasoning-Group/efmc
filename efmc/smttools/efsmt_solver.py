# coding: utf-8
import logging
import time
from typing import List

import z3
from z3.z3util import get_vars

from .mapped_blast import translate_smt2formula_to_cnf
from .smtlib_solver import SMTLIBSolver

logger = logging.getLogger(__name__)


def efsmt_solve_aux(logic: str, y: List[z3.ExprRef], phi: z3.ExprRef, maxloops=None):
    """
    A simple CEAGR-style approach for solving exists x. forall y. phi(x, y)
    It can also be understood as a "two-player game"
      x is the set of template variables (introduced by the template)
      y is the set of "program variables" (used in the original VC)
    """
    x = [item for item in get_vars(phi) if item not in y]
    if "RA" in logic:
        qf_logic = "QF_LRA"
    elif "BV" in logic:
        qf_logic = "QF_BV"
    elif "IA" in logic:
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
            # print("fsolver logic: ", get_logic(z3.And(fsolver.assertions())))
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

    def solve_with_qbf(self, y: List[z3.ExprRef], phi: z3.ExprRef):
        """
        Translate to QBF
        :param y: variables to be universal quantified
        :param phi: a quantifier-free formula
        :return: a QBF formula?
        """
        assert self.logic == "BV" or self.logic == "UFBV"
        bv2bool, id_table, header, clauses = translate_smt2formula_to_cnf(phi)
        print(bv2bool)
        print(clauses)

    def solve_with_cegar(self, y: List[z3.ExprRef], phi: z3.ExprRef):
        """
        Solve with a CEGAR-style algorithm, which consists of a "forall solver" and an "exists solver"
        :return:
        """
        """This can be slow (perhaps not a good idea for NRA) Maybe good for LRA or BV?"""
        print("User-defined EFSMT starting!!!")
        z3_res, model = efsmt_solve_aux(self.logic, y, phi)
        return z3_res, model

    def solve_with_bin_smt(self, y, phi: z3.ExprRef):
        """
        Build a quantified formula and send it to a third-party SMT solver
        that can handle quantified formulas
        :param y: the universal quantified variables
        :param phi: the quantifier-free part of the VC
        :return: TBD
        """
        smt2string = "(set-logic {})\n".format(self.logic)
        sol = z3.Solver()
        sol.add(z3.ForAll(y, phi))
        smt2string += sol.to_smt2()

        bin_cmd = f"/Users/prism/Work/cvc5/build/bin/cvc5 -q --produce-models"
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
