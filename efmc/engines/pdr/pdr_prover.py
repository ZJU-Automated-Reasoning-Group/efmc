"""
Property-Directed Reachability (or IC3)

Currently, we use the implementation inside Z3's CHC engine.
TODO: use other PDR engines
"""

import logging
import time

import z3

from efmc.sts import TransitionSystem
from efmc.utils.verification_utils import VerificationResult

logger = logging.getLogger(__name__)


class PDRProver:
    def __init__(self, system: TransitionSystem):
        self.sts = system

    def solve(self) -> VerificationResult:
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
        elif self.sts.has_bool:
            for _ in range(len(self.sts.variables)): inv_sig += "z3.BoolSort(), "
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
        res = s.check()
        if res == z3.sat:
            print("PDR time: ", time.time() - start)
            print("safe")
            invariant = s.model().eval(inv(self.sts.variables))
            print("Invariant: ", invariant)
            return VerificationResult(True, invariant)
        elif res == z3.unsat:
            print("PDR time: ", time.time() - start)
            print("unsafe")
            return VerificationResult(False, None)
        else:
            print("PDR time: ", time.time() - start)
            print("unknown")
            return VerificationResult(False, None, None, is_unknown=True)
