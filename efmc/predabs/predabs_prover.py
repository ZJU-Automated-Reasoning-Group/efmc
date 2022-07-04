# coding: utf-8
# import time
import logging
from itertools import chain
from itertools import combinations
from typing import List

import z3

from ..sts import TransitionSystem
from ..utils import negate, is_sat, is_valid, ctx_simplify

"""
This is an "old-school" version of the predicate abstraction domain.

- A set of predicates is given prior. The element in the domain is the Boolean combination of those predicates
- Compute the strongest post operation(similar to symbolic abstraction)
- Compute inductive invariant expressed in the element of the domain 
Currently we do not explore
- Lazy abstraction, lazy abstraction with interpolation, etc...
"""

logger = logging.getLogger(__name__)


def eval_preds(m: z3.ModelRef, predicates: List[z3.BoolRef]) -> List:
    """ Let m be a model of a formula phi. preds be a set of predicates"""
    res = []
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
def strongest_consequence(fml: z3.ExprRef, predicates: List, k=None) -> z3.ExprRef:
    """
    Compute the strongest necessary condition of fml that is the Boolean combination of preds
    Following CAV'06 paper "SMT Techniques for Fast Predicate Abstraction"
    """
    s = z3.Solver()
    s.add(fml)
    res = []
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
    notfml = negate(fml)
    sc = strongest_consequence(notfml, predicates)
    return z3.simplify(z3.Not(sc))


def stronget_consequence_simple(phi: z3.ExprRef, predicates: List[z3.ExprRef]) -> z3.ExprRef:
    """Is this correct?"""
    res = z3.And(False)
    neg_preds = map(lambda xx: z3.Not(xx), predicates)

    for ps in combinations(chain(predicates, neg_preds), len(list(predicates))):  # for py3?
        if is_sat(z3.And(phi, *ps)):
            res = z3.Or(res, z3.And(*ps))

    return z3.simplify(res)


def fixpoint(old_inv: z3.ExprRef, inv: z3.ExprRef) -> bool:
    return is_valid(z3.Implies(inv, old_inv))


class PredicateAbstractionProver(object):
    def __init__(self, system: TransitionSystem):
        self.sts = system
        self.preds = []

        """
        var_map = [(x, xp), (y, yp)]
        var_map_rev = [(xp ,x), (yp, y)]
        """
        self.var_map = []
        self.var_map_rev = []
        for i in range(len(self.sts.variables)):
            self.var_map.append((self.sts.variables[i], self.sts.prime_variables[i]))
            self.var_map_rev.append((self.sts.prime_variables[i], self.sts.variables[i]))

    def set_predicates(self, predicates: List):
        """
        The element in the domain is the Boolean combinations of a set of predicates
        """
        self.preds = predicates

    def solve(self):
        preds_prime = []
        for pred in self.preds:
            preds_prime.append(z3.substitute(pred, self.var_map))

        old_inv = False
        inv = self.sts.init
        i = 0
        while not fixpoint(old_inv, inv):
            print("\nInv at ", i, ": ", inv)
            i = i + 1
            # onestep = stronget_consequence_simple(And(inv, trans), preds_prime) # another imple
            onestep = strongest_consequence(z3.And(inv, self.sts.trans), preds_prime)
            onestep = z3.substitute(onestep, self.var_map_rev)
            old_inv = inv  # Is this correct?
            inv = z3.simplify(z3.Or(inv, onestep))
        # print("\n")

        if is_valid(z3.Implies(inv, self.sts.post)):
            print(ctx_simplify(inv))
            print(">>> SAFE\n\n")
        else:
            print(">>> MAYBE?!?!\n\n")

        return


if __name__ == '__main__':
    x, y, z, xp, yp, zp = z3.Reals("x y z x! y! z!")

    init = x == 0
    trans = z3.And(x < 10, xp == x + 1)
    post = z3.Implies(x >= 10, x == 10)
    # preds = [x == 10, x > 10]

    # preds = [x >= 0, x == y]
    preds = [x < 10, x == 10]
    all_vars = [x, xp]
    sts = TransitionSystem()
    sts.from_z3_cnts([all_vars, init, trans, post])

    pp = PredicateAbstractionProver(sts)
    pp.set_predicates(preds)
    pp.solve()
