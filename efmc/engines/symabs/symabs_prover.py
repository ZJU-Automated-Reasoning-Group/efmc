"""
This is an "old-school" version of symbolic abstraction domain.
"""
import logging

import z3

from efmc.sts import TransitionSystem
from efmc.utils import is_valid

logger = logging.getLogger(__name__)


############################
def strongest_consequence(fml: z3.ExprRef, domain: str, k=None) -> z3.ExprRef:
    """
    """
    raise NotImplementedError


def fixpoint(old_inv: z3.ExprRef, inv: z3.ExprRef) -> bool:
    """Decide whether reaching a fixpoint or not..
    TODO: is this true? (e.g. should we check for equivalence?)"""
    return is_valid(z3.Implies(inv, old_inv))

class SymbolicAbstractionProver(object):
    def __init__(self, system: TransitionSystem):
        self.sts = system
        """
        var_map = [(x, xp), (y, yp)]
        var_map_rev = [(xp ,x), (yp, y)]
        """
        self.var_map = []
        self.var_map_rev = []
        for i in range(len(self.sts.variables)):
            self.var_map.append((self.sts.variables[i], self.sts.prime_variables[i]))
            self.var_map_rev.append((self.sts.prime_variables[i], self.sts.variables[i]))

    def solve(self):
        """External interface for verification"""
        preds_prime = []
        for pred in self.preds:
            preds_prime.append(z3.substitute(pred, self.var_map))

        old_inv = False
        inv = self.sts.init
        i = 0
        while not fixpoint(old_inv, inv):
            print("\nInv at ", i, ": ", inv)
            i = i + 1
            # onestep = strongest_consequence_simple(And(inv, trans), preds_prime) # another imple
            onestep = strongest_consequence(z3.And(inv, self.sts.trans), preds_prime)
            onestep = z3.substitute(onestep, self.var_map_rev)
            old_inv = inv  # Is this correct?
            inv = z3.simplify(z3.Or(inv, onestep))
        # print("\n")

        # check whether the invariant is precise enough
        if is_valid(z3.Implies(inv, self.sts.post)):
            print(z3.simplify(inv))
            print(">>> SAFE\n\n")
        else:
            # need refinement
            print(">>> MAYBE?!?!\n\n")

        return
