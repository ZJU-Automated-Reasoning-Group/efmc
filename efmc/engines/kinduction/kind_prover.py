"""
Ported from https://github.com/pysmt/pysmt/blob/97c6eda689bbc7707602c2b3a3e1444f9d75166d/examples/model_checking.py

TODO:
   - Different approaches for creating vars and exprs
   - Incremental version (e.g., build the exprs incrementally, and use incremental solving)
   - Parallel k-induction
   - Use auxiliary invariants (e.g., generated by the template-based approach)
   - Forward + backward?
"""
import logging
from functools import lru_cache

import z3

from efmc.engines.kinduction.aux_invariant_generator import InvariantGenerator
# from typing import List
from efmc.sts import TransitionSystem
from efmc.utils.z3_solver_utils import is_unsat

logger = logging.getLogger(__name__)


class KInductionProver(object):
    """
    k-induction
    This one is non-incremental
    """

    def __init__(self, system: TransitionSystem):
        """Init"""
        self.sts = system
        self.use_aux_invariant = False  # use aux invariant generate by other tools
        self.aux_invariant = None

        self.use_bv = system.has_bv
        if self.use_bv:

            # FIXME: this is not a good idea, as different variables
            #  can have different sizes
            self.bv_size = system.variables[0].size()
        self.use_int = system.has_int
        self.use_real = system.has_real
        self.use_bool = system.has_bool

        self.init_0 = z3.substitute(self.sts.init, self.get_subs(0))
        self.unrolled_system = []  # T(0,1) & T(1,2) & ... & T(k-1,k)
        self.k_hypothesis = []

    def next_var(self, var: z3.ExprRef) -> z3.ExprRef:
        """Returns the 'next' of the given variable"""
        if self.use_bv:
            return z3.BitVec("{}!".format(str(var)), self.bv_size)
        elif self.use_int:
            return z3.Int("%s!" % str(var))
        elif self.use_real:
            return z3.Real("%s!" % str(var))
        elif self.use_bool:
            return z3.Bool("%s!" % str(var))
        else:
            raise NotImplementedError

    def at_time(self, var, t: int):
        """Builds an SMT variable representing v at time t"""
        if self.use_bv:
            return z3.BitVec("{0}@{1}".format(str(var), t), self.bv_size)
        elif self.use_int:
            return z3.Int("{0}@{1}".format(str(var), t))
        elif self.use_real:
            return z3.Real("{0}@{1}".format(str(var), t))
        elif self.use_bool:
            return z3.Bool("{0}@{1}".format(str(var), t))
        else:
            raise NotImplementedError
        # return z3.Int("%s@%d" % (str(variable), t))

    @lru_cache(maxsize=None)
    def get_subs(self, i):
        """Builds a map from x to x@i and from x' to x@(i+1), for all x in system."""
        # TODO: use some cache
        subs_i = []
        # for variable in self.sts.variables:
        #    subs_i.append((variable, self.at_time(variable, i)))
        #    subs_i.append((self.next_var(variable), self.at_time(variable, i + 1)))
        # FIXME: the following code assumes that self.sts.variables and self.sts.prime_variables have the same size,
        #  and the order of the variables are preserved, e.g, [x, y, z] and [x!, y!, z!]
        for j in range(len(self.sts.variables)):
            subs_i.append((self.sts.variables[j], self.at_time(self.sts.variables[j], i)))
            subs_i.append((self.sts.prime_variables[j], self.at_time(self.sts.variables[j], i + 1)))
        return subs_i

    def get_unrolling(self, k):
        """Unrolling of the transition relation from 0 to k:
        E.g. T(0,1) & T(1,2) & ... & T(k-1,k)
        for i in range(k + 1):
            subs_i = self.get_subs(i)
            res.append(z3.substitute(self.sts.trans, subs_i))
        """
        if k == 0:
            self.unrolled_system.append(z3.substitute(self.sts.trans, self.get_subs(0)))
        else:
            self.unrolled_system.append(z3.substitute(self.sts.trans, self.get_subs(k)))
        return self.unrolled_system

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

    def get_k_hypothesis(self, k: int):
        """Hypothesis for k-induction: each state up to k-1 fulfills the property
        res = []
        for i in range(k):
            subs_i = self.get_subs(i)
            res.append(z3.substitute(self.sts.post, subs_i))
        return res
        """
        if k == 0:
            return self.k_hypothesis  # or return [] (the hypo is empty when k = 0)
        self.k_hypothesis.append(z3.substitute(self.sts.post, self.get_subs(k - 1)))
        return self.k_hypothesis

    def strength_via_invariant(self, k: int):
        """Strength the k-hypothesis via aux invariant (e.g., generated by
           abstract interpretation, constraint-based approach, etc.)"""
        assert self.use_aux_invariant
        res = []
        for i in range(k + 1):
            # TODO: First, is this correct?
            #   Second, add the res to the solver
            subs_i = self.get_subs(i)
            res.append(z3.substitute(self.aux_invariant, subs_i))
        return res

    def get_bmc(self, k: int):
        """Returns the BMC encoding at step k"""
        prop_k = z3.substitute(self.sts.post, self.get_subs(k))
        return z3.And(z3.And(self.get_unrolling(k)), self.init_0, z3.Not(prop_k))

    def get_k_induction(self, k: int):
        """Returns the K-Induction encoding at step K"""
        # FIXME
        prop_k = z3.substitute(self.sts.post, self.get_subs(k))
        if self.use_aux_invariant:
            k_aux_inv = self.strength_via_invariant(k)
            print("Aux invariant: ", k_aux_inv)
            # TODO: add k_aux_inv to the following formula? (need to check correctness first..)

        return z3.And(z3.And(self.get_unrolling(k)),
                      z3.And(self.get_k_hypothesis(k)),
                      self.get_simple_path(k),
                      z3.Not(prop_k))

    def solve(self, k: int):
        """Interleaves BMC and K-Ind to verify the property."""

        if self.use_aux_invariant:
            # print("Generating aux invariant..")
            inv_gen = InvariantGenerator(self.sts)
            aux_inv = inv_gen.generate_via_ef()
            # print("aux inv", aux_inv)
            if not z3.is_true(aux_inv):
                self.aux_invariant = aux_inv
            else:
                self.use_aux_invariant = False  # the invariant generator does not work

        print("Checking property %s..." % str(self.sts.post))
        for b in range(k):
            f_bmc = self.get_bmc(b)
            logger.debug("   [BMC]    Checking bound %d..." % (b + 1))
            s = z3.Solver()
            s.add(f_bmc)
            if s.check() == z3.sat:
                print("--> Bug found at step %d" % (b + 1))
                # print(s.model())
                print("unsafe")
                return "unsafe"

            f_kind = self.get_k_induction(b)
            logger.debug("   [K-IND]  Checking bound %d..." % (b + 1))
            if is_unsat(f_kind):
                print("--> The system is proved safe at {}".format((b + 1)))
                print("safe")
                return "safe"
        print("unknown")
        return "unknown"
