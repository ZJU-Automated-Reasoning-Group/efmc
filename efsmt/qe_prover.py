# coding: utf-8
import time
from z3 import *
from .sts import TransitionSystem
from .utils import *

"""
Use quantifier elimination to compute the strongest inductive invariant?
- The abstract transformer is strongest
- The invariant is also?

TODO: this can be very slow; besides, it does not consider the ...
"""


def fixpoint(old_inv: z3.ExprRef, inv: z3.ExprRef):
    return is_valid(Implies(inv, old_inv))


class QuantifierElminationProver:
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
            qfml = Exists(self.sts.variables, And(inv, self.sts.trans))
            # compute the best abstract transformer
            onestep = Tactic('qe2')(qfml).as_expr()  # sometimes, 'qe' is better
            # rename
            onestep = substitute(onestep, self.var_map_rev)
            old_inv = inv  # Is this correct?
            inv = simplify(Or(inv, onestep))
            # inv = ctx_simplify(Or(inv, onestep))
        # print("\n")

        if is_valid(Implies(inv, post)):
            print(">>> SAFE\n\n")
            print("QE success time: ", time.time() - start)
            print("Invariant: ", simplify(inv))
        else:
            # FIXME: I think QE-based invariant inference is "sound and complete"
            # FIXME: If the invariant cannot prove the post, the program is unsafe.
            print(">>> UNSAFE \n\n")
            print("QE UNSAFE time: ", time.time() - start)
        return


if __name__ == '__main__':
    x, y, z, xp, yp, zp = Reals("x y z x! y! z!")

    init = x == 0
    trans = And(x < 10, xp == x + 1)
    post = Implies(x >= 10, x == 10)
    vars = [x, xp]
    sts = TransitionSystem()
    sts.from_z3_cnts([vars, init, trans, post])

    pp = QuantifierElminationProver(sts)
    pp.solve()
