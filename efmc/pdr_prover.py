# coding: utf-8
import time
import logging
from z3 import *
from .sts import TransitionSystem

"""
Property-Directed Reachability (or IC3)

Currently, we use the implementation inside Z3's CHC engine.
"""

logger = logging.getLogger(__name__)


class PDRProver:
    def __init__(self, sts: TransitionSystem):
        self.sts = sts

    def solve(self):
        """From transition system to CHC"""
        assert self.sts.initialized
        s = SolverFor("HORN")
        # construct the "inv" uninterpreted function
        # FIXME: the following is ugly
        inv_sig = "Function(\'inv\', "
        for _ in range(len(self.sts.variables)): inv_sig += "RealSort(),"
        inv_sig += "BoolSort())"
        inv = eval(inv_sig)

        # Init
        s.add(ForAll(self.sts.variables, Implies(self.sts.init,
                                                 inv(self.sts.variables))))
        # Inductive
        s.add(ForAll(self.sts.all_variables, Implies(And(inv(self.sts.variables), self.sts.trans),
                                                     inv(self.sts.prime_variables))))
        # Post
        s.add(ForAll(self.sts.variables, Implies(inv(self.sts.variables),
                                                 self.sts.post)))

        print("PDR starting!!!")
        # print(s.to_smt2())
        start = time.time()
        if s.check() == sat:
            print("PDR success time: ", time.time() - start)
            print("Invariant: ", s.model().eval(inv(self.sts.variables)))
        else:
            print("PDR fail time: ", time.time() - start)
            print("PDR fails to prove")
        print("")
