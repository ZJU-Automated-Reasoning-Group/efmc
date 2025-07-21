"""
Implementation of "Inductive Invariant Generation via Abductive Inference" (OOPSLA'13)

This module implements an algorithm that uses abductive inference to automatically generate
inductive invariants for transition systems by iteratively strengthening candidate invariants
through abduction until finding an inductive invariant that proves the desired safety property.
"""

import logging
from typing import Tuple, Optional
import time

import z3

from efmc.engines.abduction.abductor.abductor import qe_abduce
from efmc.sts import TransitionSystem
from efmc.utils.verification_utils import VerificationResult, SolverTimeout, check_entailment, \
    are_expressions_equivalent, check_invariant

logger = logging.getLogger(__name__)


class AbductionProver:
    """Implements invariant generation using abductive inference."""

    def __init__(self, system: TransitionSystem, max_iterations: int = 300):
        self.sts = system
        self.max_iterations = max_iterations
        self.var_map = list(zip(self.sts.variables, self.sts.prime_variables))
        self.var_map_rev = list(zip(self.sts.prime_variables, self.sts.variables))
        self.last_cti = None

    def check_inductiveness(self, inv: z3.ExprRef) -> Tuple[bool, Optional[z3.ModelRef]]:
        """Check if the candidate invariant is inductive: I ∧ T → I'"""
        inv_prime = z3.substitute(inv, self.var_map)
        s = z3.Solver()
        s.add(inv, self.sts.trans, z3.Not(inv_prime))
        result = s.check()
        return result == z3.unsat, s.model() if result == z3.sat else None

    def strengthen_from_cti(self, inv: z3.ExprRef, cti: z3.ModelRef) -> z3.ExprRef:
        """Strengthen the invariant using a counterexample to inductiveness."""
        self.last_cti = cti

        # Extract pre-state constraints from CTI
        pre_state_constraints = [v == cti[v] for v in self.sts.variables if v in cti]
        pre_state = z3.And(*pre_state_constraints) if pre_state_constraints else z3.BoolVal(True)

        # Set up abduction query
        pre_cond = z3.And(inv, pre_state, self.sts.trans)
        post_cond = z3.substitute(inv, self.var_map)

        try:
            strengthening = qe_abduce(pre_cond, post_cond)
            if strengthening is None:
                return self._generalize_strengthening(inv, pre_state, cti)
            
            new_inv = z3.simplify(z3.And(inv, strengthening))
            
            # Verify strengthening excludes CTI and isn't False
            s = z3.Solver()
            s.add(new_inv, pre_state)
            if s.check() == z3.sat or z3.is_false(new_inv):
                return self._generalize_strengthening(inv, pre_state, cti)
            
            return new_inv
        except Exception as e:
            logger.warning(f"Abduction error: {e}. Using targeted exclusion.")
            return self._generalize_strengthening(inv, pre_state, cti)

    def _generalize_strengthening(self, inv: z3.ExprRef, pre_state: z3.ExprRef, cti: z3.ModelRef) -> z3.ExprRef:
        """Apply targeted strengthening based on generalizing from the CTI."""
        # Try inequality constraints for numeric variables
        constraints = []
        for v in self.sts.variables:
            if v in cti and str(v) in str(inv):
                val = cti[v]
                if z3.is_int_value(val):
                    val_int = val.as_long()
                    if val_int > 0:
                        constraints.append(v <= val_int - 1)
                    elif val_int < 0:
                        constraints.append(v >= val_int + 1)
                    else:
                        constraints.extend([v > 0, v < 0])
                elif z3.is_bool(val):
                    constraints.append(z3.Not(v) if z3.is_true(val) else v)

        # Try generalized constraints
        if constraints:
            for combiner in [z3.Or, z3.And]:
                new_inv = z3.simplify(z3.And(inv, combiner(*constraints)))
                s = z3.Solver()
                s.add(new_inv, pre_state)
                if s.check() == z3.unsat and not z3.is_false(new_inv):
                    return new_inv

        # Fallback: exclude specific variable values
        exclusions = [v != cti[v] for v in self.sts.variables if v in cti]
        if exclusions:
            new_inv = z3.simplify(z3.And(inv, z3.Or(*exclusions)))
            if not z3.is_false(new_inv):
                return new_inv

        logger.warning("Could not find suitable strengthening. Returning original invariant.")
        return inv

    def invgen(self, overall_timeout: Optional[int] = None) -> Optional[z3.ExprRef]:
        """Generate an inductive invariant using abduction-based refinement."""
        start_time = time.time()
        inv = self.sts.post
        past_invariants = set()
        
        for iteration in range(self.max_iterations):
            # Check timeout
            if overall_timeout and time.time() - start_time > overall_timeout:
                raise SolverTimeout("Overall algorithm timeout")
            
            inv = z3.simplify(inv)
            if z3.is_false(inv) or str(inv) in past_invariants:
                return None
            past_invariants.add(str(inv))
            
            # Check initiation: init => inv
            s = z3.Solver()
            s.add(self.sts.init, z3.Not(inv))
            if s.check() == z3.sat:
                cex = s.model()
                state_constraints = [v == cex[v] for v in self.sts.variables if v in cex]
                state = z3.And(*state_constraints) if state_constraints else z3.BoolVal(True)
                
                # Strengthen based on initiation counterexample
                if inv.decl().kind() == z3.Z3_OP_AND:
                    new_conjuncts = []
                    for conjunct in inv.children():
                        s.push()
                        s.add(self.sts.init, state, z3.Not(conjunct))
                        if s.check() == z3.sat:
                            new_conjuncts.append(z3.Or(conjunct, z3.Not(state)))
                        else:
                            new_conjuncts.append(conjunct)
                        s.pop()
                    inv = z3.And(*new_conjuncts) if new_conjuncts else inv
                else:
                    old_inv = inv
                    inv = z3.simplify(z3.And(inv, z3.Not(state)))
                    if z3.is_false(inv):
                        return None
                continue
            
            # Check safety: inv => post
            if not check_entailment(inv, self.sts.post):
                return None
            
            # Check inductiveness
            inductive, cti = self.check_inductiveness(inv)
            if inductive:
                return inv
            
            if cti is None:
                return None
            
            # Strengthen using CTI
            new_inv = self.strengthen_from_cti(inv, cti)
            if are_expressions_equivalent(new_inv, inv):
                return None
            
            inv = new_inv
        
        return None

    def solve(self, timeout: Optional[int] = None) -> VerificationResult:
        """Verify the system using abductive invariant generation."""
        try:
            inv = self.invgen(overall_timeout=timeout)
            if inv is not None:
                return VerificationResult(True, inv)
            
            # Check if last CTI represents a safety violation
            if self.last_cti is not None:
                pre_state_constraints = [v == self.last_cti[v] for v in self.sts.variables if v in self.last_cti]
                pre_state = z3.And(*pre_state_constraints) if pre_state_constraints else z3.BoolVal(True)
                
                s = z3.Solver()
                s.add(pre_state, z3.Not(self.sts.post))
                if s.check() == z3.sat:
                    return VerificationResult(False, None, self.last_cti, is_unsafe=True)
                else:
                    return VerificationResult(False, None, self.last_cti, is_unknown=True)
            
            return VerificationResult(False, None, None, is_unknown=True)
        except SolverTimeout:
            return VerificationResult(False, None, None, is_unknown=True, timed_out=True)
        except Exception as e:
            logger.error(f"Verification error: {e}")
            return VerificationResult(False, None, None, is_unknown=True)
