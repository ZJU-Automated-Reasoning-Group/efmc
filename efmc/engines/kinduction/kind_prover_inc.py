"""
Incremental k-induction prover using two solvers for efficient incremental solving.
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
    """k-induction prover with incremental solving using separate BMC and inductive solvers."""

    def __init__(self, system: TransitionSystem, show_model=False):
        self.sts = system
        self.show_model = show_model
        
        # Initialize caches
        self._var_cache = {}
        self._sub_cache = {}
        self.unrolled_system = []
        self.k_hypothesis = []

        # Determine variable type and size
        self.var_types = {
            'bv': system.has_bv,
            'int': system.has_int, 
            'real': system.has_real,
            'bool': system.has_bool
        }
        self.bv_size = system.variables[0].sort().size() if self.var_types['bv'] else None

        # Create solvers
        self.solver_bmc = z3.Solver()
        self.solver_kind = z3.Solver()

        # Add initial state to BMC solver
        self.init_0 = z3.substitute(self.sts.init, self.get_subs(0))
        self.solver_bmc.add(self.init_0)

        # Auxiliary invariant setup
        self.use_aux_invariant = False
        self.aux_invariant = None

    def _create_var(self, name: str):
        """Create variable based on system type"""
        if self.var_types['bv']:
            return z3.BitVec(name, self.bv_size)
        elif self.var_types['int']:
            return z3.Int(name)
        elif self.var_types['real']:
            return z3.Real(name)
        elif self.var_types['bool']:
            return z3.Bool(name)
        else:
            raise NotImplementedError("Unsupported variable type")

    def at_time(self, var, t: int):
        """Get variable at time t with caching"""
        key = (str(var), t)
        if key not in self._var_cache:
            self._var_cache[key] = self._create_var(f"{str(var)}@{t}")
        return self._var_cache[key]

    @lru_cache(maxsize=None)
    def get_subs(self, i: int):
        """Get substitutions for time i to i+1 with caching"""
        if i not in self._sub_cache:
            subs = []
            for j, var in enumerate(self.sts.variables):
                subs.extend([
                    (var, self.at_time(var, i)),
                    (self.sts.prime_variables[j], self.at_time(var, i + 1))
                ])
            self._sub_cache[i] = subs
        return self._sub_cache[i]

    def get_unrolling(self, k):
        """Get transition unrolling from 0 to k"""
        while len(self.unrolled_system) <= k:
            i = len(self.unrolled_system)
            self.unrolled_system.append(z3.substitute(self.sts.trans, self.get_subs(i)))
        return z3.And(*self.unrolled_system[:k])

    def get_simple_path(self, k):
        """Generate simple path constraint for k-induction"""
        constraints = []
        for i in range(k):
            for j in range(i + 1, k + 1):
                state_diff = [self.at_time(var, i) != self.at_time(var, j) 
                             for var in self.sts.variables]
                constraints.append(z3.Or(*state_diff))
        return z3.And(*constraints) if constraints else z3.BoolVal(True)

    def get_k_hypothesis(self, k: int):
        """Get k-induction hypothesis: P(0) & P(1) & ... & P(k)"""
        while len(self.k_hypothesis) <= k:
            i = len(self.k_hypothesis)
            self.k_hypothesis.append(z3.substitute(self.sts.post, self.get_subs(i)))
        return z3.And(*self.k_hypothesis[:k + 1])

    def get_aux_invariants(self, k: int):
        """Get auxiliary invariants for strengthening"""
        if not self.use_aux_invariant or self.aux_invariant is None:
            return z3.BoolVal(True)
        
        aux_invs = [z3.substitute(self.aux_invariant, self.get_subs(i)) 
                   for i in range(k + 1)]
        return z3.And(*aux_invs)

    def get_k_induction_formula(self, k: int):
        """Build complete k-induction formula"""
        return z3.And(
            self.get_k_hypothesis(k),
            self.get_unrolling(k + 1),
            z3.Not(z3.substitute(self.sts.post, self.get_subs(k + 1))),
            self.get_simple_path(k + 1),
            self.get_aux_invariants(k + 1)
        )

    def _setup_aux_invariant(self):
        """Setup auxiliary invariant if needed"""
        if not self.use_aux_invariant:
            return
            
        logger.info("Generating auxiliary invariant...")
        inv_gen = InvariantGenerator(self.sts)
        aux_inv = inv_gen.generate_via_ef()
        logger.info("Generated auxiliary invariant: %s", aux_inv)
        
        if not z3.is_true(aux_inv):
            self.aux_invariant = aux_inv
        else:
            self.use_aux_invariant = False
            logger.info("Trivial invariant generated, disabling auxiliary invariants")

    def solve(self, k: int = 10, timeout: Optional[int] = None) -> VerificationResult:
        """Perform k-induction proof using incremental solving"""
        start_time = time.time()
        self._setup_aux_invariant()
        
        logger.info("Checking property %s...", str(self.sts.post))

        for b in range(k):
            # Check timeout
            if timeout and time.time() - start_time > timeout:
                logger.info("Timeout reached after %d seconds", timeout)
                return VerificationResult(False, None, None, is_unknown=True, is_timeout=True)

            # BMC check
            logger.debug("   [BMC]    Checking bound %d...", b + 1)
            self.solver_bmc.push()
            self.solver_bmc.add(z3.Not(z3.substitute(self.sts.post, self.get_subs(b))))
            
            if self.solver_bmc.check() == z3.sat:
                logger.info("--> Bug found at step %d", b + 1)
                model = self.solver_bmc.model()
                
                if self.show_model:
                    logger.info("Model (counterexample):")
                    for i in range(b + 2):
                        logger.info("State %d:", i)
                        for var in self.sts.variables:
                            var_at_time = self.at_time(var, i)
                            try:
                                val = model.eval(var_at_time)
                                if val is not None:
                                    logger.info("  %s = %s", var, val)
                            except:
                                # Skip variables that don't have values in the model
                                pass
                
                logger.info("unsafe")
                return VerificationResult(False, None, model, is_unsafe=True)
            
            self.solver_bmc.pop()

            # K-induction check
            logger.debug("   [K-IND]  Checking bound %d...", b + 1)
            s_kind = z3.Solver()
            s_kind.add(self.get_k_induction_formula(b))
            
            if s_kind.check() == z3.unsat:
                logger.info("--> The system is proved safe at %d", b + 1)
                logger.info("safe")
                return VerificationResult(True, self.sts.post)

            # Add transition for next iteration
            if b < k - 1:
                trans_k = z3.substitute(self.sts.trans, self.get_subs(b))
                self.solver_bmc.add(trans_k)
                self.unrolled_system.append(trans_k)

        logger.info("unknown")
        return VerificationResult(False, None, None, is_unknown=True)


def main():
    """Example usage of the incremental k-induction prover"""
    x, y, _p_x, _p_y = z3.Reals('x y x! y!')
    init = z3.And(x == 0, y == 8)
    trans = z3.Or(z3.And(x < 8, y <= 8, _p_x == x + 2, _p_y == y - 2), 
                  z3.And(x == 8, _p_x == 0, y == 0, _p_y == 8))
    post = z3.Not(z3.And(x == 0, y == 0))
    
    from efmc.sts import TransitionSystem
    sts = TransitionSystem()
    sts.from_z3_cnts([[x, y], [_p_x, _p_y], init, trans, post])
    
    prover = KInductionProverInc(sts, show_model=True)
    result = prover.solve(k=10, timeout=60)
    print(f"Result: {result}")


if __name__ == '__main__':
    main()
