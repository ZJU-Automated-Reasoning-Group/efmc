# coding: utf-8
import time
import logging
import z3
from ..sts import TransitionSystem
from ..utils import is_valid

"""
Use quantifier elimination to compute the strongest inductive invariant?
- The abstract transformer is strongest
- The invariant is also?

  TODO: this can be very slow; besides, it does not consider the ...
"""

logger = logging.getLogger(__name__)


def fixpoint(old_inv: z3.ExprRef, inv: z3.ExprRef):
    return is_valid(z3.Implies(inv, old_inv))


class QuantifierEliminationProver:
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
        start = time.time()
        old_inv = False
        inv = self.sts.init
        i = 0
        print("QE-based invariant inference starting!!!")
        while not fixpoint(old_inv, inv):
            print("\nInv at ", i, ": ", inv)
            i = i + 1
            qfml = z3.Exists(self.sts.variables, z3.And(inv, self.sts.trans))
            # compute the best abstract transformer
            onestep = z3.Tactic('qe2')(qfml).as_expr()  # sometimes, 'qe' is better
            # rename
            onestep = z3.substitute(onestep, self.var_map_rev)
            old_inv = inv  # Is this correct?
            inv = z3.simplify(z3.Or(inv, onestep))
            # inv = ctx_simplify(Or(inv, onestep))
        # print("\n")

        if is_valid(z3.Implies(inv, post)):
            print(">>> SAFE\n\n")
            print("QE success time: ", time.time() - start)
            print("Invariant: ", z3.simplify(inv))
        else:
            # FIXME: I think QE-based invariant inference is "sound and complete"
            # FIXME: If the invariant cannot prove the post, the program is unsafe.
            print(">>> UNSAFE \n\n")
            print("QE UNSAFE time: ", time.time() - start)
        return


if __name__ == '__main__':
    x, y, z, xp, yp, zp = z3.Reals("x y z x! y! z!")

    init = x == 0
    trans = z3.And(x < 10, xp == x + 1)
    post = z3.Implies(x >= 10, x == 10)
    all_vars = [x, xp]
    sts = TransitionSystem()
    sts.from_z3_cnts([all_vars, init, trans, post])

    pp = QuantifierEliminationProver(sts)
    pp.solve()
