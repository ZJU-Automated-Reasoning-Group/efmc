"""
Non-incremental k-induction prover.

TODO:
   - Incremental version
   - Parallel k-induction
   - Use auxiliary invariants
   - Forward + backward
"""
import logging
import time
from functools import lru_cache
from typing import Optional, List, Tuple, Dict, Any

import z3

from efmc.engines.kinduction.aux_invariant_generator import InvariantGenerator
from efmc.sts import TransitionSystem
from efmc.utils.z3_solver_utils import is_unsat
from efmc.engines.abduction.abduction_prover import VerificationResult

logger = logging.getLogger(__name__)


class KInductionProver:
    """Non-incremental k-induction prover."""

    def __init__(self, system: TransitionSystem, show_model: bool = False):
        self.sts = system
        self.show_model = show_model
        self.use_aux_invariant = False
        self.aux_invariant: Optional[z3.ExprRef] = None

        # Variable type handling
        self.var_types: Dict[str, bool] = {
            'bv': system.has_bv,
            'int': system.has_int,
            'real': system.has_real,
            'bool': system.has_bool,
            'fp': system.has_fp
        }
        self.bv_size: Optional[int] = system.variables[0].size() if self.var_types['bv'] else None
        self.fp_sort: Optional[z3.FPSortRef] = system.variables[0].sort() if self.var_types['fp'] else None

        # Initialize cached structures
        self.init_0 = z3.substitute(self.sts.init, self.get_subs(0))
        self.unrolled_system: List[z3.ExprRef] = []
        self.k_hypothesis: List[z3.ExprRef] = []

    def _create_var(self, name: str) -> z3.ExprRef:
        """Create variable based on system type"""
        if self.var_types['bv']:
            return z3.BitVec(name, self.bv_size)
        elif self.var_types['int']:
            return z3.Int(name)
        elif self.var_types['real']:
            return z3.Real(name)
        elif self.var_types['bool']:
            return z3.Bool(name)
        elif self.var_types['fp']:
            return z3.FP(name, self.fp_sort)
        else:
            raise NotImplementedError("Unsupported variable type")

    def at_time(self, var: z3.ExprRef, t: int) -> z3.ExprRef:
        """Create SMT variable representing var at time t"""
        return self._create_var(f"{str(var)}@{t}")

    @lru_cache(maxsize=None)
    def get_subs(self, i: int) -> List[Tuple[z3.ExprRef, z3.ExprRef]]:
        """Build substitutions from x to x@i and x' to x@(i+1)"""
        subs: List[Tuple[z3.ExprRef, z3.ExprRef]] = []
        for j, var in enumerate(self.sts.variables):
            subs.extend([
                (var, self.at_time(var, i)),
                (self.sts.prime_variables[j], self.at_time(var, i + 1))
            ])
        return subs

    def get_unrolling(self, k: int) -> z3.ExprRef:
        """Get transition unrolling T(0,1) & T(1,2) & ... & T(k-1,k)"""
        while len(self.unrolled_system) <= k:
            i = len(self.unrolled_system)
            self.unrolled_system.append(z3.substitute(self.sts.trans, self.get_subs(i)))
        return z3.And(*self.unrolled_system[:k])

    def get_simple_path(self, k: int) -> z3.ExprRef:
        """Generate simple path constraint - each state must be different"""
        constraints: List[z3.ExprRef] = []
        for i in range(k):
            for j in range(i + 1, k + 1):
                state_diff = [self.at_time(var, i) != self.at_time(var, j) 
                             for var in self.sts.variables]
                constraints.append(z3.Or(*state_diff))
        return z3.And(*constraints) if constraints else z3.BoolVal(True)

    def get_k_hypothesis(self, k: int) -> z3.ExprRef:
        """Get k-induction hypothesis: P(0) & P(1) & ... & P(k)"""
        while len(self.k_hypothesis) <= k:
            i = len(self.k_hypothesis)
            self.k_hypothesis.append(z3.substitute(self.sts.post, self.get_subs(i)))
        return z3.And(*self.k_hypothesis[:k + 1])

    def get_aux_invariants(self, k: int) -> z3.ExprRef:
        """Get auxiliary invariants for strengthening"""
        if not self.use_aux_invariant or self.aux_invariant is None:
            return z3.BoolVal(True)
        
        aux_invs = [z3.substitute(self.aux_invariant, self.get_subs(i)) 
                   for i in range(k + 1)]
        return z3.And(*aux_invs)

    def get_bmc_formula(self, k: int) -> z3.ExprRef:
        """Build BMC formula for step k"""
        return z3.And(
            self.init_0, 
            self.get_unrolling(k), 
            z3.Not(z3.substitute(self.sts.post, self.get_subs(k)))
        )

    def get_k_induction_formula(self, k: int) -> z3.ExprRef:
        """Build complete k-induction formula"""
        return z3.And(
            self.get_k_hypothesis(k),
            self.get_unrolling(k),
            z3.Not(z3.substitute(self.sts.post, self.get_subs(k + 1))),
            self.get_simple_path(k + 1),
            self.get_aux_invariants(k + 1)
        )

    def _setup_aux_invariant(self) -> None:
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
        """Interleave BMC and K-induction to verify the property"""
        start_time = time.time()
        self._setup_aux_invariant()
        
        logger.info("Checking property %s...", str(self.sts.post))
        
        # Try BMC first
        for step in range(1, k + 1):
            logger.info(f"BMC step {step}")
            bmc_formula = self.get_bmc_formula(step)
            
            s = z3.Solver()
            if timeout:
                s.set("timeout", timeout * 1000)
            s.add(bmc_formula)
            
            if s.check() == z3.sat:
                logger.info(f"Property violation found at BMC step {step}")
                if self.show_model:
                    model = s.model()
                    logger.info(f"Counterexample: {model}")
                return VerificationResult(False, None, is_unsafe=True)
        
        # Try k-induction
        for step in range(1, k + 1):
            logger.info(f"K-induction step {step}")
            ki_formula = self.get_k_induction_formula(step)
            
            s = z3.Solver()
            if timeout:
                s.set("timeout", timeout * 1000)
            s.add(ki_formula)
            
            if s.check() == z3.unsat:
                logger.info(f"Property proven safe with k-induction step {step}")
                # Extract invariant from the proof
                invariant = self.get_k_hypothesis(step)
                return VerificationResult(True, invariant)
        
        logger.info("Could not prove or disprove the property")
        return VerificationResult(False, None, is_unknown=True)
