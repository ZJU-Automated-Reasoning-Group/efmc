"""
A simple CEAGR-style approach for solving exists x. forall y. phi(x, y)
It can also be understood as a "two-player game".

In the context of template-based (or "constraint-based") invariant generation,
  x is the set of template variables (introduced by the template)
  y is the set of "program variables" (used in the original VC)

TODO: maybe use PySMT to support other backend?
"""

from typing import List
import z3
from z3.z3util import get_vars


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
