# coding: utf-8
# import time
import logging
from z3 import *
from itertools import combinations
from itertools import chain
from typing import List

from .sts import TransitionSystem
from .utils import *

"""
This is an "old-school" version of the predicate abstraction domain.

- A set of predicates is given prior. The element in the domain is the Boolean combination of those predicates
- Compute the strongest post operation(similar to symbolic abstraction)
- Compute inductive invariant expressed in the element of the domain 
Currently we do not explore
- Lazy abstraction, lazy abstraction with interpolation, etc...
"""

logger = logging.getLogger(__name__)


def eval_preds(m: ModelRef, predicates: List[z3.BoolRef]):
    """ Let m be a model of a formula phi. preds be a set of predicates"""
    res = []
    for p in predicates:
        if is_true(m.eval(p)):
            res.append(p)
        elif is_false(m.eval(p)):
            res.append(negate(p))
        else:
            pass
    return res


############################
# predicate abstraction
def strongest_consequence(fml, predicates, k=None):
    """
    Compute the strongest necessary condition of fml that is the Boolean combination of preds
    Following CAV'06 paper "SMT Techniques for Fast Predicate Abstraction"
    """
    s = Solver()
    s.add(fml)
    res = []
    while s.check() == sat:
        m = s.model()
        # "generalizes" from the current model????
        # TODO: use prime implicate (i.e., throwing away some p in preds)
        proj = And(eval_preds(m, predicates))
        res.append(proj)
        # block the current one
        s.add(negate(proj))

    return simplify(Or(res))


def weakest_sufficient_condition(fml, preds):
    notfml = Not(fml)
    sc = strongest_consequence(notfml, preds)
    return simplify(Not(sc))


def stronget_consequence_simple(phi, preds):
    """Is this correct?"""
    res = And(False)
    negpreds = map(lambda xx: Not(xx), preds)

    for ps in combinations(chain(preds, negpreds), len(list(preds))):  # for py3?
        if is_sat(And(phi, *ps)):
            res = Or(res, And(*ps))

    return simplify(res)


def fixpoint(old_inv, inv):
    return is_valid(Implies(inv, old_inv))


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

    def set_predicates(self, preds):
        """
        The element in the domain is the Boolean combinations of a set of predicates
        """
        self.preds = preds

    def solve(self):
        preds_prime = []
        for pred in self.preds:
            preds_prime.append(substitute(pred, self.var_map))

        old_inv = False
        inv = self.sts.init
        i = 0
        while not fixpoint(old_inv, inv):
            print("\nInv at ", i, ": ", inv)
            i = i + 1
            # onestep = stronget_consequence_simple(And(inv, trans), preds_prime) # another imple
            onestep = strongest_consequence(And(inv, self.sts.trans), preds_prime)
            onestep = substitute(onestep, self.var_map_rev)
            old_inv = inv  # Is this correct?
            inv = simplify(Or(inv, onestep))
        # print("\n")

        if is_valid(Implies(inv, self.sts.post)):
            print(ctx_simplify(inv))
            print(">>> SAFE\n\n")
        else:
            print(">>> MAYBE?!?!\n\n")

        return


if __name__ == '__main__':
    x, y, z, xp, yp, zp = Reals("x y z x! y! z!")

    init = x == 0
    trans = And(x < 10, xp == x + 1)
    post = Implies(x >= 10, x == 10)
    preds = [x == 10, x > 10]

    # preds = [x >= 0, x == y]
    preds = [x < 10, x == 10]
    vars = [x, xp]
    sts = TransitionSystem()
    sts.from_z3_cnts([vars, init, trans, post])

    pp = PredicateAbstractionProver(sts)
    pp.set_predicates(preds)
    pp.solve()
