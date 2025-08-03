"""
This is an "old-school" version of the predicate abstraction domain.

- A set of predicates is given prior. The element in the domain is the Boolean combination of those predicates
- Compute the strongest post operation(similar to symbolic abstraction)
- Compute inductive invariant expressed in the element of the domain
Currently we do not explore
- Lazy abstraction, lazy abstraction with interpolation, etc...

TODO: use more "advanced" CEGAR engines
"""

import logging
from itertools import chain, combinations
from typing import List, Optional

import z3

from efmc.sts import TransitionSystem
from efmc.utils import negate, is_sat, is_valid
from efmc.utils.z3_solver_utils import fixpoint
from efmc.utils.verification_utils import VerificationResult

logger = logging.getLogger(__name__)


def eval_preds(m: z3.ModelRef, predicates: List[z3.BoolRef]) -> List[z3.ExprRef]:
    """ Let m be a model of a formula phi. preds be a set of predicates"""
    res: List[z3.ExprRef] = []
    for p in predicates:
        if z3.is_true(m.eval(p)):
            res.append(p)
        elif z3.is_false(m.eval(p)):
            res.append(negate(p))
        else:
            pass
    return res


############################
# predicate abstraction
def strongest_consequence(fml: z3.ExprRef, predicates: List[z3.ExprRef], k: Optional[int] = None) -> z3.ExprRef:
    """
    Compute the strongest necessary condition of fml that is the Boolean combination of preds
    Following CAV'06 paper "SMT Techniques for Fast Predicate Abstraction"
    """
    s = z3.Solver()
    s.add(fml)
    res: List[z3.ExprRef] = []
    while s.check() == z3.sat:
        m = s.model()
        # "generalizes" from the current model????
        # TODO: use prime implicate (i.e., throwing away some p in preds)
        proj = z3.And(eval_preds(m, predicates))
        res.append(proj)
        # block the current one
        s.add(negate(proj))

    return z3.simplify(z3.Or(res))


def weakest_sufficient_condition(fml: z3.ExprRef, predicates: List[z3.ExprRef]) -> z3.ExprRef:
    """Compute WSC using the duality between SNC(Strongest Necessary Condition)"""
    sc = strongest_consequence(negate(fml), predicates)
    return z3.simplify(z3.Not(sc))


def stronget_consequence_simple(phi: z3.ExprRef, predicates: List[z3.ExprRef]) -> z3.ExprRef:
    """Is this correct?"""
    res = z3.And(False)
    neg_preds = map(lambda xx: z3.Not(xx), predicates)

    for ps in combinations(chain(predicates, neg_preds), len(list(predicates))):  # for py3?
        if is_sat(z3.And(phi, *ps)):
            res = z3.Or(res, z3.And(*ps))

    return z3.simplify(res)


class PredicateAbstractionProver(object):
    def __init__(self, system: TransitionSystem):
        self.sts = system
        self.preds: List[z3.ExprRef] = []

        """
        var_map = [(x, xp), (y, yp)]
        var_map_rev = [(xp ,x), (yp, y)]
        """
        self.var_map: List = []
        self.var_map_rev: List = []
        for i in range(len(self.sts.variables)):
            self.var_map.append((self.sts.variables[i], self.sts.prime_variables[i]))
            self.var_map_rev.append((self.sts.prime_variables[i], self.sts.variables[i]))

    def set_predicates(self, predicates: List[z3.ExprRef]) -> None:
        """The element in the domain is the Boolean combinations of a set of predicates"""
        self.preds = predicates

    def solve(self, timeout: Optional[int] = None) -> VerificationResult:
        """Main solving procedure for predicate abstraction"""
        # TODO: implement the actual predicate abstraction algorithm
        # For now, just return unknown
        return VerificationResult(False, None, is_unknown=True)
