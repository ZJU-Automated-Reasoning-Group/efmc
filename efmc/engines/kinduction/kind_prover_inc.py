"""
Incremental k-induction prover that follows the same interface as the non-incremental version.

This implementation uses two solvers for efficient incremental solving:
  - solver1 for BMC (base case)
  - solver2 for k-induction (inductive case)

Optimizations:
- Incremental solving with push/pop
- Variable creation cache
- Substitution cache
- Leveraging @lru_cache
- Auxiliary invariant integration
"""
import logging
import time
from typing import Optional
from functools import lru_cache

import z3

from efmc.engines.kinduction.aux_invariant_generator import InvariantGenerator
from efmc.sts import TransitionSystem
from efmc.utils.z3_solver_utils import is_unsat
from efmc.engines.abduction.abduction_prover import VerificationResult

logger = logging.getLogger(__name__)


class KInductionProverInc:
    """
    k-induction prover with incremental solving.
    Uses two separate solvers for the base case and inductive step.
    """

    def __init__(self, system: TransitionSystem, show_model=False):
        """Initialize the incremental k-induction prover"""
        self.sts = system
        self.show_model = show_model
        
        # Initialize caches
        self._var_at_time_cache = {}
        self._substitution_cache = {}
        self.unrolled_system = []  # T(0,1) & T(1,2) & ... & T(k-1,k)
        self.k_hypothesis = []

        # Determine variable types
        self.use_bv = system.has_bv
        self.use_int = system.has_int
        self.use_real = system.has_real
        self.use_bool = system.has_bool
        if self.use_bv:
            self.bv_size = system.variables[0].sort().size()

        # Create solvers for incremental solving
        self.solver_bmc = z3.Solver()  # For BMC
        self.solver_kind = z3.Solver()  # For k-induction

        # Initialize initial state constraint
        self.init_0 = z3.substitute(self.sts.init, self.get_subs(0))
        self.solver_bmc.add(self.init_0)

        # Initialize auxiliary invariant flag
        self.use_aux_invariant = False
        self.aux_invariant = None

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
        """Builds an SMT variable representing v at time t with caching"""
        key = (str(var), t)
        if key not in self._var_at_time_cache:
            name = f"{str(var)}@{t}"
            if self.use_bv:
                result = z3.BitVec(name, self.bv_size)
            elif self.use_int:
                result = z3.Int(name)
            elif self.use_real:
                result = z3.Real(name)
            elif self.use_bool:
                result = z3.Bool(name)
            else:
                raise NotImplementedError("Unsupported variable type")
            self._var_at_time_cache[key] = result
        return self._var_at_time_cache[key]

    @lru_cache(maxsize=None)
    def get_subs(self, i: int):
        """Builds substitutions for variables at time i to i+1 with caching"""
        if i not in self._substitution_cache:
            subs = []
            for j in range(len(self.sts.variables)):
                subs.append((self.sts.variables[j], self.at_time(self.sts.variables[j], i)))
                subs.append((self.sts.prime_variables[j], self.at_time(self.sts.variables[j], i + 1)))
            self._substitution_cache[i] = subs
        return self._substitution_cache[i]

    def get_unrolling(self, k):
        """Unrolling of the transition relation from 0 to k:
        E.g. T(0,1) & T(1,2) & ... & T(k-1,k)
        
        In incremental mode, we add these constraints directly to solvers.
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
        # k-hypothesis: P(0) & P(1) & ... & P(k)
        k_hypothesis = self.get_k_hypothesis(k)
        
        # unrolling: T(0,1) & T(1,2) & ... & T(k,k+1)
        unrolling = self.get_unrolling(k + 1)
        
        # negation of property at k+1: !P(k+1)
        not_post_k_plus_1 = z3.Not(z3.substitute(self.sts.post, self.get_subs(k + 1)))
        
        # simple path constraint
        simple_path = self.get_simple_path(k + 1)
        
        # auxiliary invariants
        aux_invs = self.strength_via_invariant(k + 1)
        
        return z3.And(k_hypothesis, unrolling, not_post_k_plus_1, simple_path, aux_invs)

    def _add_transition_at_k(self, k: int):
        """Incrementally adds transition relation at step k to both solvers"""
        trans_k = z3.substitute(self.sts.trans, self.get_subs(k))
        self.solver_bmc.add(trans_k)
        self.unrolled_system.append(trans_k)
        
        # We don't add to solver_kind directly as we'll use push/pop with complete formulas

    def solve(self, k: int = 10, timeout: Optional[int] = None) -> VerificationResult:
        """
        Performs k-induction proof using incremental solving.
        
        Args:
            k: Maximum bound to check (default: 10)
            timeout: The timeout in seconds
            
        Returns:
            VerificationResult: Object containing verification result and related data
        """
        start_time = time.time()

        # Generate auxiliary invariants if requested
        if self.use_aux_invariant:
            logger.info("Generating auxiliary invariant...")
            inv_gen = InvariantGenerator(self.sts)
            aux_inv = inv_gen.generate_via_ef()
            logger.info("Generated auxiliary invariant: %s", aux_inv)
            if not z3.is_true(aux_inv):
                self.aux_invariant = aux_inv
            else:
                self.use_aux_invariant = False
                logger.info("Invariant generator produced trivial invariant, disabling auxiliary invariants")

        logger.info("Checking property %s...", str(self.sts.post))

        # The BMC solver already has init_0 added
        
        for b in range(k):
            # BMC phase: Check if property can be violated in b steps
            logger.debug("   [BMC]    Checking bound %d...", b + 1)
            
            # Push a new scope for the current BMC query
            self.solver_bmc.push()
            
            # Add the negation of property at step b
            not_post_b = z3.Not(z3.substitute(self.sts.post, self.get_subs(b)))
            self.solver_bmc.add(not_post_b)
            
            # Check if the property can be violated
            result = self.solver_bmc.check()
            
            if result == z3.sat:
                logger.info("--> Bug found at step %d", b + 1)
                model = self.solver_bmc.model()
                
                if self.show_model:
                    logger.info("Model (counterexample):")
                    for i in range(b + 2):  # Show states from 0 to b+1
                        logger.info("State %d:", i)
                        for var in self.sts.variables:
                            var_at_time = self.at_time(var, i)
                            if var_at_time in model:
                                logger.info("  %s = %s", var, model[var_at_time])
                
                logger.info("unsafe")
                return VerificationResult(False, None, model, is_unsafe=True)
            
            # Remove the negated property for the next iteration
            self.solver_bmc.pop()
            
            # K-induction phase: Check if property holds inductively
            logger.debug("   [K-IND]  Checking bound %d...", b + 1)
            
            # Create the k-induction formula for step b
            # We're not using the solver state directly for k-induction, 
            # but we're creating a complete formula each time
            f_kind = self.get_k_induction(b)
            
            # Use a fresh solver for each k-induction check
            s_kind = z3.Solver()
            s_kind.add(f_kind)
            kind_result = s_kind.check()
            
            if kind_result == z3.unsat:
                logger.info("--> The system is proved safe at %d", b + 1)
                logger.info("safe")
                # Create an invariant from the k-induction proof
                invariant = self.sts.post
                return VerificationResult(True, invariant)
            
            # Check for timeout after potentially long-running solver operations
            if timeout is not None and time.time() - start_time > timeout:
                logger.info("Timeout reached after %d seconds", timeout)
                return VerificationResult(False, None, None, is_unknown=True, is_timeout=True)
            
            # If we haven't found a result yet and this isn't the last iteration,
            # add transition for the next step
            if b < k - 1:
                self._add_transition_at_k(b)

        logger.info("unknown")
        return VerificationResult(False, None, None, is_unknown=True)


def main():
    """Example usage of the incremental k-induction prover"""
    x, y, _p_x, _p_y = z3.Reals('x y x! y!')
    init = z3.And(x == 0, y == 8)
    trans = z3.Or(z3.And(x < 8, y <= 8, _p_x == x + 2, _p_y == y - 2), 
                  z3.And(x == 8, _p_x == 0, y == 0, _p_y == 8))
    post = z3.Not(z3.And(x == 0, y == 0))  # Is valid.
    
    from efmc.sts import TransitionSystem
    sts = TransitionSystem()
    sts.from_z3_cnts([[x, y], [_p_x, _p_y], init, trans, post])
    
    prover = KInductionProverInc(sts, show_model=True)
    result = prover.solve(k=10, timeout=60)  # Set a 60-second timeout
    print(f"Result: {result}")


if __name__ == '__main__':
    main()
