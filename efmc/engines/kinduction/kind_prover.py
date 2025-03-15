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
from efmc.engines.abduction.abduction_prover import VerificationResult

logger = logging.getLogger(__name__)


class KInductionProver(object):
    """
    k-induction
    This one is non-incremental
    """

    def __init__(self, system: TransitionSystem, verbose=False, show_model=False):
        """Init"""
        self.sts = system
        self.use_aux_invariant = False  # use aux invariant generate by other tools
        self.aux_invariant = None
        self.verbose = verbose
        self.show_model = show_model

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
        """
        # Fix the unrolling implementation to ensure we have all transitions up to k
        if len(self.unrolled_system) <= k:
            for i in range(len(self.unrolled_system), k + 1):
                self.unrolled_system.append(z3.substitute(self.sts.trans, self.get_subs(i)))
        return z3.And(*self.unrolled_system[:k])

    def get_simple_path(self, k):
        """Simple path constraint for k-induction:
        Each state from 0 to k must be different from each other
        """
        constraints = []
        for i in range(k):
            for j in range(i + 1, k + 1):
                # Create a constraint that at least one variable differs between states i and j
                state_diff = []
                for var in self.sts.variables:
                    var_i = self.at_time(var, i)
                    var_j = self.at_time(var, j)
                    state_diff.append(var_i != var_j)
                constraints.append(z3.Or(*state_diff))
        return z3.And(*constraints) if constraints else z3.BoolVal(True)

    def get_k_hypothesis(self, k: int):
        """
        Compute the k-induction hypothesis: P(0) & P(1) & ... & P(k)
        """
        if len(self.k_hypothesis) <= k:
            for i in range(len(self.k_hypothesis), k + 1):
                self.k_hypothesis.append(z3.substitute(self.sts.post, self.get_subs(i)))
        return z3.And(*self.k_hypothesis[:k + 1])

    def strength_via_invariant(self, k: int):
        """
        Strengthen the k-induction hypothesis with auxiliary invariants
        """
        if not self.use_aux_invariant or self.aux_invariant is None:
            return z3.BoolVal(True)

        aux_invs = []
        for i in range(k + 1):
            aux_invs.append(z3.substitute(self.aux_invariant, self.get_subs(i)))
        return z3.And(*aux_invs)

    def get_bmc(self, k: int):
        """
        Bounded model checking formula for step k
        """
        return z3.And(self.init_0, self.get_unrolling(k), z3.Not(z3.substitute(self.sts.post, self.get_subs(k))))

    def get_k_induction(self, k: int):
        """
        k-induction formula for step k
        """
        # Base case: P(0) & P(1) & ... & P(k) & T(0,1) & ... & T(k-1,k) & !P(k+1)
        # Inductive case: P(0) & P(1) & ... & P(k) & T(0,1) & ... & T(k,k+1) & !P(k+1)
        # With simple path constraint: P(0) & P(1) & ... & P(k) & T(0,1) & ... & T(k,k+1) & !P(k+1) & simple_path(0,k+1)
        # With auxiliary invariants: P(0) & P(1) & ... & P(k) & T(0,1) & ... & T(k,k+1) & !P(k+1) & simple_path(0,k+1) & aux_inv(0) & ... & aux_inv(k+1)

        # Base case
        k_hypothesis = self.get_k_hypothesis(k)
        unrolling = self.get_unrolling(k)
        not_post_k_plus_1 = z3.Not(z3.substitute(self.sts.post, self.get_subs(k + 1)))

        # Add simple path constraint
        simple_path = self.get_simple_path(k + 1)

        # Add auxiliary invariants
        aux_invs = self.strength_via_invariant(k + 1)

        return z3.And(k_hypothesis, unrolling, not_post_k_plus_1, simple_path, aux_invs)

    def solve(self, k: int) -> VerificationResult:
        """Interleaves BMC and K-Ind to verify the property."""

        if self.use_aux_invariant:
            if self.verbose:
                print("Generating auxiliary invariant...")
            inv_gen = InvariantGenerator(self.sts)
            aux_inv = inv_gen.generate_via_ef()
            if self.verbose:
                print("Generated auxiliary invariant:", aux_inv)
            if not z3.is_true(aux_inv):
                self.aux_invariant = aux_inv
            else:
                self.use_aux_invariant = False
                if self.verbose:
                    print("Invariant generator produced trivial invariant, disabling auxiliary invariants")

        print("Checking property %s..." % str(self.sts.post))
        for b in range(k):
            f_bmc = self.get_bmc(b)
            if self.verbose:
                print(f"[BMC] Checking bound {b + 1}...")
            else:
                logger.debug("   [BMC]    Checking bound %d..." % (b + 1))

            s = z3.Solver()
            s.add(f_bmc)
            result = s.check()
            if result == z3.sat:
                print("--> Bug found at step %d" % (b + 1))
                model = s.model()
                if self.show_model:
                    print("Model (counterexample):")
                    for i in range(b + 2):  # Show states from 0 to b+1
                        print(f"State {i}:")
                        for var in self.sts.variables:
                            var_at_time = self.at_time(var, i)
                            if var_at_time in model:
                                print(f"  {var} = {model[var_at_time]}")
                print("unsafe")
                return VerificationResult(False, None, model)

            f_kind = self.get_k_induction(b)
            if self.verbose:
                print(f"[K-IND] Checking bound {b + 1}...")
            else:
                logger.debug("   [K-IND]  Checking bound %d..." % (b + 1))

            if is_unsat(f_kind):
                print("--> The system is proved safe at {}".format((b + 1)))
                print("safe")
                # Create an invariant from the k-induction proof
                invariant = self.sts.post
                return VerificationResult(True, invariant)

        print("unknown")
        return VerificationResult(False, None, None, is_unknown=True)
