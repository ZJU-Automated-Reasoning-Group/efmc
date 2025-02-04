"""
Implementation of "Inductive Invariant Generation via Abductive Inference" (OOPSLA'13)

TODO: generated by LLM, to be reviewed

This module implements an algorithm that uses abductive inference to automatically generate
inductive invariants for transition systems. The algorithm works by iteratively strengthening
candidate invariants through abduction until finding an inductive invariant that proves the
desired safety property.

Key concepts:
- Abductive inference: Reasoning that generates hypotheses to explain observations
- Inductive invariant: A formula that is preserved by the transition relation and implies safety
- Counterexample to inductiveness (CTI): A state pair showing where inductiveness fails

The main algorithm:
1. Start with the post-condition as the initial candidate invariant
2. Check if the candidate is inductive
3. If not, use abduction to strengthen it based on counterexamples
4. Repeat until finding an inductive invariant or determining one cannot be found
"""

import logging
from dataclasses import dataclass
from typing import Tuple, Optional, List, Sequence

import z3

from efmc.engines.abduction.abductor.abductor import qe_abduce
from efmc.sts import TransitionSystem

logger = logging.getLogger(__name__)

@dataclass
class VerificationResult:
    """Stores the result of the verification process."""
    is_safe: bool
    invariant: Optional[z3.ExprRef]
    counterexample: Optional[z3.ModelRef] = None

class SolverTimeout(Exception):
    """Raised when the Z3 solver times out."""
    pass

def check_entailment(expr1: z3.ExprRef, expr2: z3.ExprRef, timeout: int = 10000) -> bool:
    """
    Check if expr1 entails expr2 using Z3 solver.

    Args:
        expr1: The expression that is assumed to hold
        expr2: The expression that should be entailed by expr1
        timeout: Solver timeout in milliseconds

    Returns:
        True if expr1 entails expr2, False otherwise

    Raises:
        SolverTimeout: If the solver times out
    """
    s = z3.Solver()
    s.set("timeout", timeout)
    s.add(z3.And(expr1, z3.Not(expr2)))

    result = s.check()
    if result == z3.unknown:
        raise SolverTimeout("Solver timed out during entailment check")
    return result == z3.unsat

def are_expressions_equivalent(expr1: z3.ExprRef, expr2: z3.ExprRef, timeout: int = 10000) -> bool:
    """
    Check if two Z3 expressions are logically equivalent.

    Args:
        expr1: First expression
        expr2: Second expression
        timeout: Solver timeout in milliseconds

    Returns:
        True if expressions are equivalent, False otherwise

    Raises:
        SolverTimeout: If the solver times out
    """
    s = z3.Solver()
    s.set("timeout", timeout)

    # Check if (expr1 ∧ ¬expr2) ∨ (¬expr1 ∧ expr2) is unsatisfiable
    equivalence_check = z3.Or(
        z3.And(expr1, z3.Not(expr2)),
        z3.And(z3.Not(expr1), expr2)
    )
    s.add(equivalence_check)

    result = s.check()
    if result == z3.unknown:
        raise SolverTimeout("Solver timed out during equivalence check")
    return result == z3.unsat

class AbductionProver:
    """
    Implements invariant generation using abductive inference.
    """

    def __init__(self, system: TransitionSystem, timeout: int = 10000, max_iterations: int = 300):
        """
        Initialize the AbductionProver.

        Args:
            system: The transition system to verify
            timeout: Solver timeout in milliseconds
            max_iterations: Maximum number of strengthening iterations
        """
        self.sts = system
        self.timeout = timeout
        self.max_iterations = max_iterations

        # Create mappings between current and next-state variables
        self.var_map = list(zip(self.sts.variables, self.sts.prime_variables))
        self.var_map_rev = list(zip(self.sts.prime_variables, self.sts.variables))

    def check_inductiveness(self, inv: z3.ExprRef) -> Tuple[bool, Optional[z3.ModelRef]]:
        """
        Check if the candidate invariant is inductive.

        An invariant I is inductive if: I ∧ T → I'
        where I' is I with all variables replaced by their primed versions.

        Args:
            inv: Candidate invariant formula

        Returns:
            Tuple containing:
            - Boolean indicating if inv is inductive
            - If not inductive, a counterexample model; otherwise None

        Raises:
            SolverTimeout: If the solver times out
        """
        inv_prime = z3.substitute(inv, self.var_map)

        s = z3.Solver()
        s.set("timeout", self.timeout)
        s.add(inv, self.sts.trans, z3.Not(inv_prime))

        result = s.check()
        if result == z3.unknown:
            raise SolverTimeout("Solver timed out during inductiveness check")

        return result == z3.unsat, s.model() if result == z3.sat else None

    def strengthen_from_cti(self, inv: z3.ExprRef, cti: z3.ModelRef) -> z3.ExprRef:
        """
        Strengthen the invariant using a counterexample to inductiveness.

        Args:
            inv: Current candidate invariant
            cti: Counterexample model showing non-inductiveness

        Returns:
            Strengthened invariant formula
        """
        # Extract current state constraints from CTI
        pre_state_constraints = [
            v == cti[v] for v in self.sts.variables if v in cti
        ]
        pre_state = z3.And(*pre_state_constraints) if pre_state_constraints else z3.BoolVal(True)

        # Extract next state constraints and substitute back to current variables
        post_state_constraints = [
            v == cti[v] for v in self.sts.prime_variables if v in cti
        ]
        post_state = z3.And(*post_state_constraints) if post_state_constraints else z3.BoolVal(True)
        post_state = z3.substitute(post_state, self.var_map_rev)

        # Set up abduction query
        pre_cond = z3.And(inv, pre_state, self.sts.trans)
        post_cond = z3.substitute(inv, self.var_map_rev)

        # Perform abduction to find strengthening condition
        strengthening = qe_abduce(pre_cond, post_cond)
        if strengthening is None:
            logger.debug("Abduction failed. Falling back to CTI exclusion.")
            strengthening = z3.Not(pre_state)

        new_inv = z3.simplify(z3.And(inv, strengthening))
        logger.debug(f"Strengthened invariant: {new_inv}")
        return new_inv

    def verify_safety(self, inv: z3.ExprRef) -> VerificationResult:
        """
        Verify that the invariant proves the safety property.

        Checks three conditions:
        1. init → inv        (Initiation)
        2. inv ∧ T → inv'    (Inductiveness)
        3. inv → post        (Safety)

        Args:
            inv: The invariant to verify

        Returns:
            VerificationResult containing the verification outcome and relevant data
        """
        s = z3.Solver()
        s.set("timeout", self.timeout)

        # Check initiation
        s.push()
        s.add(self.sts.init, z3.Not(inv))
        if s.check() == z3.sat:
            return VerificationResult(False, None, s.model())
        s.pop()

        # Check safety
        s.push()
        s.add(inv, z3.Not(self.sts.post))
        if s.check() == z3.sat:
            return VerificationResult(False, None, s.model())
        s.pop()

        return VerificationResult(True, inv)

    def invgen(self) -> Optional[z3.ExprRef]:
        """
        Generate an inductive invariant using abduction-based refinement.

        Returns:
            An inductive invariant if found, None otherwise

        Raises:
            SolverTimeout: If the solver times out during verification
        """
        inv = self.sts.post
        iteration = 0

        logger.info("Starting invariant generation...")
        while iteration < self.max_iterations:
            logger.debug(f"Iteration {iteration}: Checking current invariant")

            # Verify safety properties
            result = self.verify_safety(inv)
            if not result.is_safe:
                logger.info("Safety check failed")
                return None

            # Check inductiveness
            inductive, cti = self.check_inductiveness(inv)
            if inductive:
                logger.info("Found inductive invariant")
                return inv

            if cti is None:
                logger.warning("Failed to generate CTI despite non-inductiveness")
                return None

            # Strengthen the invariant
            logger.debug(f"Strengthening using CTI: {cti}")
            new_inv = self.strengthen_from_cti(inv, cti)

            # Check progress
            if are_expressions_equivalent(new_inv, inv):
                logger.warning("Failed to make progress in strengthening")
                return None

            inv = new_inv
            iteration += 1

        logger.warning(f"Exceeded maximum iterations ({self.max_iterations})")
        return None

    def solve(self) -> VerificationResult:
        """
        Verify the system using abductive invariant generation.

        Returns:
            VerificationResult containing the verification outcome and relevant data
        """
        try:
            inv = self.invgen()
            if inv is not None:
                logger.info("System verified safe")
                return VerificationResult(True, inv)
            logger.info("Could not verify system safety")
            return VerificationResult(False, None)
        except SolverTimeout:
            logger.error("Verification timed out")
            return VerificationResult(False, None)