# coding: utf-8
import logging
import time

import z3

from efmc.sts import TransitionSystem

"""
Property-Directed Reachability (or IC3)

Currently, we use the implementation inside Z3's CHC engine.
"""

logger = logging.getLogger(__name__)


class PDRProver:
    def __init__(self, system: TransitionSystem):
        self.sts = system

    def solve(self):
        """From transition system to CHC"""
        assert self.sts.initialized

        # construct the "inv" uninterpreted function
        s = z3.SolverFor("HORN")
        inv_sig = "z3.Function(\'inv\', "

        if self.sts.has_int:
            for _ in range(len(self.sts.variables)): inv_sig += "z3.IntSort(), "
        elif self.sts.has_real:
            for _ in range(len(self.sts.variables)): inv_sig += "z3.RealSort(), "
        elif self.sts.has_bv:
            bv_size = self.sts.variables[0].sort().size()
            for _ in range(len(self.sts.variables)): inv_sig += "z3.BitVecSort({}), ".format(str(bv_size))
        else:
            raise NotImplementedError

        inv_sig += "z3.BoolSort())"
        inv = eval(inv_sig)
        # Init
        s.add(z3.ForAll(self.sts.variables, z3.Implies(self.sts.init,
                                                       inv(self.sts.variables))))
        # Inductive
        s.add(z3.ForAll(self.sts.all_variables, z3.Implies(z3.And(inv(self.sts.variables), self.sts.trans),
                                                           inv(self.sts.prime_variables))))
        # Post
        s.add(z3.ForAll(self.sts.variables, z3.Implies(inv(self.sts.variables),
                                                       self.sts.post)))

        print("PDR starting!!!")
        # print(s.to_smt2())
        start = time.time()
        if s.check() == z3.sat:
            print("PDR success time: ", time.time() - start)
            print("Invariant: ", s.model().eval(inv(self.sts.variables)))
        else:
            print("PDR fail time: ", time.time() - start)
            print("PDR fails to prove")
        print("")
