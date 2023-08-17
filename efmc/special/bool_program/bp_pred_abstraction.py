"""
Verifying Boolean Programs using "Predicate abstraction"

 Given a set of Boolean variables/Predicates P = {p1, ..., pn} and a transition system S,
 it finds the strongest inductive invariant expressible as a Boolean combination of P.
 E.g.,
   - p1 and p2 and p3
   - (not p1) and (p2 or p3)
"""

from typing import List

import z3

from efmc.sts import BooleanProgram
from efmc.utils import negate, is_valid, ctx_simplify, eval_predicates


def strongest_consequence(fml: z3.ExprRef, predicates: List[z3.ExprRef], k=None):
    """
    Compute the strongest necessary condition (i.e., strongest consequence)
    of `fml` that is expressive as a Boolean combination of  `predicates`

    Following CAV'06 paper "SMT Techniques for Fast Predicate Abstraction"
    NOTE: in some contexts, "predicate abstraction" also means this function,
    """
    s = z3.Solver()
    s.add(fml)
    res = []
    while s.check() == z3.sat:
        m = s.model()
        # each proj is a sufficient (or necessary?) condition that
        # "generalizes" from the current model????
        # TODO: use prime implicate (i.e., throwing away some p in preds)
        proj = z3.And(eval_predicates(m, predicates))
        res.append(proj)
        # block the current one
        s.add(negate(proj))

    return z3.simplify(z3.Or(res))


def weakest_sufficient_condition(fml: z3.ExprRef, predicates: List[z3.ExprRef]):
    """Following the duality of WSC and SNC"""
    notfml = z3.Not(fml)
    sc = strongest_consequence(notfml, predicates)
    return z3.simplify(z3.Not(sc))


def fixpoint(old_inv: z3.ExprRef, inv: z3.ExprRef) -> bool:
    return is_valid(z3.Implies(inv, old_inv))


class BoolAbstractionProver:
    def __init__(self, system: BooleanProgram):
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

    def set_predicates(self, predicates):
        """The element in the domain is the Boolean combinations of a set of predicates"""
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
    x, y, xp, yp = z3.Bools("x y x! y!")
    init = z3.And(x, y)
    trans = z3.And(z3.Implies(y, xp == y, yp == y), z3.Implies(z3.Not(y), xp == z3.Not(y), yp == y))
    post = x
    preds = [x, y]

    all_vars = [x, y, xp, yp]
    sts = BooleanProgram()
    sts.from_z3_cnts([all_vars, init, trans, post])

    pp = BoolAbstractionProver(sts)
    pp.set_predicates(preds)
    pp.solve()