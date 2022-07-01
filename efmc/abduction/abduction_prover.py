# coding: utf-8
import logging

import z3

from ..sts import TransitionSystem
from .abduction import dillig_abduce

"""
Implementation of the following paper:

    Inductive Invariant Generation via Abductive Inference. OOPSLA'13
    
(TODO: not finished yet)
"""

logger = logging.getLogger(__name__)


class AbductionProver(object):

    def __init__(self, system: TransitionSystem):
        """
        var_map = [(x, xp), (y, yp)]
        var_map_rev = [(xp ,x), (yp, y)]
        """
        self.sts = system
        self.var_map = []
        self.var_map_rev = []
        for i in range(len(self.sts.variables)):
            self.var_map.append((self.sts.variables[i], self.sts.prime_variables[i]))
            self.var_map_rev.append((self.sts.prime_variables[i], self.sts.variables[i]))

    def check_inductiveness(self, inv: z3.ExprRef):
        """
        Check whether the generated invariant is correct
        """
        inv_in_prime_vars = z3.substitute(inv, self.var_map)
        s = z3.Solver()
        s.add(z3.Not(z3.Implies(z3.And(self.sts.trans, inv), inv_in_prime_vars)))
        if s.check() == z3.sat:
            # not inductive; return a counterexample to inductiveness (CTI)
            model = s.model()
            return False, model
        return True, None

    def strength(self, inv: z3.ExprRef):
        """
        inductive strengthening of candidates (by abduction)
        """

        return

    def invgen(self):
        """
        In Dillig's approach, sufficiency is guaranteed by the abductive inference??
        """
        pre_cond = self.sts.init
        post_cond = self.sts.post
        inv = self.sts.post
        while True:
            ind, cti = self.check_inductiveness(inv)
            if not ind:
                print(cti)
                # TODO: need to "cover" the counterexample
                # inv \land ? |= inv'
                # inv = self.strength(inv)
                inv = dillig_abduce(pre_cond, post_cond)  # is this correct?
                # Use CTI to "refine"; find xx that is inductive relative to ....
            else:
                break
        return inv

    def verify(self):
        return
