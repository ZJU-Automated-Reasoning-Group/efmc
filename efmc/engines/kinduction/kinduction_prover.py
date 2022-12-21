"""
Ported from https://github.com/pysmt/pysmt/blob/97c6eda689bbc7707602c2b3a3e1444f9d75166d/examples/model_checking.py

For incremental k-induction, we may refer to
   https://github.com/SRI-CSL/sally/blob/80f19306bed842e7a706f178cc5e2972d342482c/src/engine/kind/kind_engine.cpp

TODO:
   Different approaches for creating vars and exprs
   Incremental version
   Parallel version
   Integrated into our main interface (kinduction_prover.py)
"""
import logging
from functools import lru_cache
import z3
# from typing import List
from efmc.sts import TransitionSystem

logger = logging.getLogger(__name__)


def is_sat(phi: z3.ExprRef) -> bool:
    s = z3.Solver()
    s.add(phi)
    return s.check() == z3.sat


def is_unsat(phi: z3.ExprRef) -> bool:
    s = z3.Solver()
    s.add(phi)
    return s.check() == z3.unsat


class KInductionProver(object):
    """
    k-induction
    This one is non-incremental
    """
    def __init__(self, system: TransitionSystem):
        self.sts = system
        self.use_bv = system.has_bv
        if self.use_bv:
            self.bv_size = system.variables[0].size()  # FIXME: nota good idea
        self.use_int = system.has_int
        self.user_real = system.has_real

    def next_var(self, var: z3.ExprRef) -> z3.ExprRef:
        """Returns the 'next' of the given variable"""
        if self.use_bv:
            return z3.BitVec("{}!".format(str(var)), self.bv_size)
        elif self.use_int:
            return z3.Int("%s!" % str(var))
        elif self.user_real:
            return z3.Real("%s!" % str(var))
        else:
            raise NotImplementedError

    def at_time(self, var, t: int):
        """Builds an SMT variable representing v at time t"""
        if self.use_bv:
            return z3.BitVec("{0}@{1}".format(str(var), t), self.bv_size)
        elif self.use_int:
            return z3.Int("{0}@{1}".format(str(var), t))
        elif self.user_real:
            return z3.Real("{0}@{1}".format(str(var), t))
        else:
            raise NotImplementedError
        # return z3.Int("%s@%d" % (str(variable), t))

    @lru_cache(maxsize=None)
    def get_subs(self, i):
        """Builds a map from x to x@i and from x' to x@(i+1), for all x in system."""
        # TODO: use some cache
        subs_i = []
        for variable in self.sts.variables:
            subs_i.append((variable, self.at_time(variable, i)))
            subs_i.append((self.next_var(variable), self.at_time(variable, i + 1)))
        return subs_i

    @lru_cache(maxsize=None)
    def get_unrolling(self, k):
        """Unrolling of the transition relation from 0 to k:
        E.g. T(0,1) & T(1,2) & ... & T(k-1,k)

        for i in range(k + 1):
            subs_i = self.get_subs(i)
            res.append(z3.substitute(self.sts.trans, subs_i))
        return res
        """
        res = []
        if k == 0:
            res.append(z3.substitute(self.sts.trans, self.get_subs(0)))
        else:
            for e in self.get_unrolling(k - 1):
                res.append(e)
            res.append(z3.substitute(self.sts.trans, self.get_subs(k)))
        return res

    def get_simple_path(self, k):
        """Simple path constraint for k-induction:
           each time encodes a different state
           TODO: simplify a bit?..
        """
        res = []
        for i in range(k + 1):
            subs_i = self.get_subs(i)
            for j in range(i + 1, k + 1):
                state = []
                subs_j = self.get_subs(j)
                for var in self.sts.variables:
                    v_i = z3.substitute(var, subs_i)
                    v_j = z3.substitute(var, subs_j)
                    state.append(v_i != v_j)
                res.append(z3.Or(state))
        return z3.And(res)

    @lru_cache(maxsize=None)
    def get_k_hypothesis(self, k: int):
        """Hypothesis for k-induction: each state up to k-1 fulfills the property
        for i in range(k):
            subs_i = self.get_subs(i)
            res.append(z3.substitute(self.sts.post, subs_i))
        """
        res = []
        if k == 0:
            return res
        else:
            for e in self.get_k_hypothesis(k - 1):
                res.append(e)
            res.append(z3.substitute(self.sts.post, self.get_subs(k - 1)))
        return res

    def get_bmc(self, k: int):
        """Returns the BMC encoding at step k"""
        init_0 = z3.substitute(self.sts.init, self.get_subs(0))
        prop_k = z3.substitute(self.sts.post, self.get_subs(k))
        return z3.And(z3.And(self.get_unrolling(k)), init_0, z3.Not(prop_k))

    def get_k_induction(self, k: int):
        """Returns the K-Induction encoding at step K"""
        # FIXME
        subs_k = self.get_subs(k)
        prop_k = z3.substitute(self.sts.post, subs_k)
        return z3.And(z3.And(self.get_unrolling(k)),
                      z3.And(self.get_k_hypothesis(k)),
                      self.get_simple_path(k),
                      z3.Not(prop_k))

    def solve(self, k: int):
        """Interleaves BMC and K-Ind to verify the property."""
        # FIXME
        print("Checking property %s..." % self.sts.post)
        for b in range(k):
            f_bmc = self.get_bmc(b)
            print("   [BMC]    Checking bound %d..." % (b + 1))
            if is_sat(f_bmc):
                print("--> Bug found at step %d" % (b + 1))
                # print(f_bmc)
                return "UNSAFE"

            f_kind = self.get_k_induction(b)
            print("   [K-IND]  Checking bound %d..." % (b + 1))
            if is_unsat(f_kind):
                print("--> The system is safe!")
                return "SAFE"
        return "UNKNOWN"

