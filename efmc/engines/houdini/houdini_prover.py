"""
Houdini-based invariant inference engine.

Houdini is a counterexample-guided inductive generalization algorithm
that finds the maximal inductive subset of a given set of candidate lemmas.
"""

import logging
import time
from typing import List, Dict, Optional

import z3

from efmc.sts import TransitionSystem
from efmc.utils.verification_utils import VerificationResult, check_invariant
from efmc.engines.houdini.houdini_templates import get_selector_var, generate_basic_lemmas


class HoudiniProver:
    """Houdini-based invariant inference engine"""

    def __init__(self, system: TransitionSystem):
        self.sts = system
        self.logger = logging.getLogger(__name__)

    def houdini(self, lemmas: List[z3.ExprRef], timeout: Optional[int] = None) -> Optional[Dict[int, z3.ExprRef]]:
        """Find the maximal inductive subset for the given lemmas"""
        annotated: List[z3.ExprRef] = []
        annotated_primes: List[z3.ExprRef] = []
        indexed: Dict[int, z3.ExprRef] = {}
        
        start_time = time.time()
        self.logger.info(f"Starting Houdini with {len(lemmas)} lemmas" + 
                        (f" (timeout: {timeout}s)" if timeout else ""))

        # Create primed versions and selector variables
        for i in range(len(lemmas)):
            lemma = lemmas[i]
            primed = z3.substitute(lemma, list(zip(self.sts.variables, self.sts.prime_variables)))
            annotated.append(z3.Or(lemma, get_selector_var(i)))
            annotated_primes.append(z3.Or(primed, get_selector_var(i)))
            indexed[i] = lemma

        prover = z3.Solver()
        prover.add(self.sts.trans)
        prover.add(z3.And(annotated))
        prover.add(z3.Not(z3.And(annotated_primes)))

        iteration = 0
        initial_count = len(indexed)

        while prover.check() != z3.unsat:
            if timeout and (time.time() - start_time > timeout):
                self.logger.warning(f"Houdini timed out after {iteration} iterations")
                return None
                
            iteration += 1
            m = prover.model()
            removed = 0

            for i in list(indexed.keys()):
                if z3.is_false(m.eval(annotated_primes[i])):
                    prover.add(get_selector_var(i))
                    del indexed[i]
                    removed += 1

            self.logger.info(f"Iteration {iteration}: Removed {removed}, {len(indexed)}/{initial_count} remaining")

        elapsed = time.time() - start_time
        self.logger.info(f"Houdini completed in {elapsed:.2f}s with {len(indexed)}/{initial_count} lemmas")
        return indexed

    def solve(self, timeout: Optional[int] = None) -> VerificationResult:
        """Main solving procedure"""
        start_time = time.time()
        
        # Check if post-condition is already inductive
        post_primed = z3.substitute(self.sts.post, list(zip(self.sts.variables, self.sts.prime_variables)))
        if check_invariant(self.sts, self.sts.post, post_primed):
            self.logger.info("Post-condition is already inductive")
            return VerificationResult(True, self.sts.post)

        # Generate and process candidate lemmas
        lemmas = self.generate_candidate_lemmas()
        result = self.houdini(lemmas, timeout)

        if result is None or (timeout and (time.time() - start_time > timeout)):
            self.logger.warning(f"Solver timed out after {time.time() - start_time:.2f}s")
            return VerificationResult(False, None, is_unknown=True, timed_out=True)

        if result:
            inv = z3.And(*result.values())
            inv_primed = z3.substitute(inv, list(zip(self.sts.variables, self.sts.prime_variables)))
            if check_invariant(self.sts, inv, inv_primed):
                self.logger.info("Found inductive invariant")
                return VerificationResult(True, inv)

        self.logger.info("Could not find inductive invariant")
        return VerificationResult(False, None, is_unknown=True)

    def generate_candidate_lemmas(self) -> List[z3.ExprRef]:
        """Generate candidate lemmas for invariant inference"""
        # Get existing invariants if available
        existing_invariants = None
        if hasattr(self.sts, 'invariants') and self.sts.invariants:
            existing_invariants = self.sts.invariants
        
        # Use the centralized lemma generation function
        lemmas = generate_basic_lemmas(
            self.sts.variables, 
            self.sts.post, 
            existing_invariants
        )
        
        self.logger.info(f"Generated {len(lemmas)} candidate lemmas")
        return lemmas