"""
Common verification utilities for transition systems.

This module provides common data structures and functions for verification tasks:
- VerificationResult: Data class for storing verification results
- SolverTimeout: Exception for solver timeouts
- check_entailment: Function to check logical entailment
- are_expressions_equivalent: Function to check logical equivalence
- check_invariant: Function to verify if an invariant is correct
- get_counterexample: Function to get a counterexample for a formula
"""

import logging
from dataclasses import dataclass
from typing import Optional, TYPE_CHECKING, Any

import z3

# Remove the direct import to break the circular dependency
# from efmc.sts import TransitionSystem
from efmc.utils.z3_solver_utils import is_entail

logger = logging.getLogger(__name__)


@dataclass
class VerificationResult:
    """
    Stores the result of the verification process.
    
    Fields:
        is_safe: True if the system is proven safe, False otherwise
        is_unsafe: True if the system is proven unsafe (counterexample exists), False otherwise
        is_unknown: True if the safety status could not be determined, False otherwise
        invariant: The inductive invariant if the system is safe, None otherwise
        counterexample: A counterexample if the system is unsafe, None otherwise
        timed_out: True if the verification process timed out, False otherwise
        
    Note: At most one of is_safe, is_unsafe, and is_unknown should be True.
    """
    is_safe: bool
    invariant: Optional[z3.ExprRef]
    counterexample: Optional[z3.ModelRef] = None
    is_unknown: bool = False
    is_unsafe: bool = False
    timed_out: bool = False
    
    def __post_init__(self):
        """Validate the verification result."""
        # If we have a counterexample, the system should be unsafe
        if self.counterexample is not None:
            self.is_unsafe = True
            
        # If the verification timed out, mark it as unknown
        if self.timed_out:
            self.is_unknown = True
            
        # Ensure consistency of the result
        safety_flags = [self.is_safe, self.is_unsafe, self.is_unknown]
        if sum(safety_flags) != 1:
            logger.warning(f"Inconsistent verification result: {safety_flags}")


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


def get_counterexample(formula: z3.ExprRef):
    """
    Get a counterexample for the given formula.
    
    Args:
        formula: The formula to find a counterexample for
        
    Returns:
        A model satisfying the formula if one exists, None otherwise
    """
    s = z3.Solver()
    s.add(formula)
    if s.check() == z3.sat:
        return s.model()
    return None


def check_invariant(sts: Any, inv: z3.ExprRef, inv_in_prime_variables: z3.ExprRef):
    """
    Check whether the generated invariant is correct.
    
    Verifies three conditions:
    1. Initiation: init => inv
    2. Inductiveness: inv && trans => inv'
    3. Safety: inv => post
    
    Args:
        sts: The transition system
        inv: The invariant to check
        inv_in_prime_variables: The invariant with variables replaced by primed versions
        
    Returns:
        True if the invariant is correct, False otherwise
    """
    correct = True

    # 1. Check initiation: init => inv
    if not is_entail(sts.init, inv):
        correct = False
        logger.error("Initiation check failed")
        model = get_counterexample(z3.And(sts.init, z3.Not(inv)))
        if model:
            logger.error(f"Counterexample: {model}")

    # 2. Check inductiveness: inv && trans => inv'
    if not is_entail(z3.And(sts.trans, inv), inv_in_prime_variables):
        correct = False
        logger.error("Inductiveness check failed")
        model = get_counterexample(z3.And(sts.trans, inv, z3.Not(inv_in_prime_variables)))
        if model:
            logger.error(f"Counterexample: {model}")

    # 3. Check safety/sufficiency: inv => post
    # NOTICE: here the guard "C" in Hoare logic is "moved" to the transition relation,
    # and we can just check is_entail(inv, sts.post) for correctness.
    if hasattr(sts, 'ignore_post_cond') and (not sts.ignore_post_cond) and (not is_entail(inv, sts.post)):
        # for some applications, we may ignore the post condition
        correct = False
        logger.error("Safety check failed")
        model = get_counterexample(z3.And(inv, z3.Not(sts.post)))
        if model:
            logger.error(f"Counterexample: {model}")

    if not correct:
        logger.debug(f"Init: {sts.init}")
        logger.debug(f"Trans: {sts.trans}")
        logger.debug(f"Post: {sts.post}")
        logger.debug(f"Inv: {inv}")
    else:
        logger.info("Invariant verification successful")

    return correct
