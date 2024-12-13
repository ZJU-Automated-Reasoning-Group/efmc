"""
Implementation of the following paper:
    Inductive Invariant Generation via Abductive Inference. OOPSLA'13

(TODO: not finished yet)

The algorithm uses abductive inference to strengthen candidate invariants until finding
an inductive invariant that proves the property.
"""

import logging
from typing import Tuple, Optional

import z3

from efmc.engines.abduction.abductor.abductor import qe_abduce
from efmc.sts import TransitionSystem

logger = logging.getLogger(__name__)


def check_entailment(expr1: z3.ExprRef, expr2: z3.ExprRef, timeout=10000) -> bool:
    """
    Check if expr1 entails expr2 using Z3 solver.

    Args:
        expr1 (z3.ExprRef): The expression that is assumed to hold.
        expr2 (z3.ExprRef): The expression that is to be entailed by expr1.
        timeout (int): Solver timeout in milliseconds.

    Returns:
        bool: True if expr1 entails expr2, False otherwise.
    """
    s = z3.Solver()
    # s.set("timeout", timeout)
    entailment_check = z3.And(expr1, z3.Not(expr2))
    s.add(entailment_check)
    result = s.check()
    if result == z3.unsat:
        return True
    elif result == z3.sat:
        return False
    else:
        logger.warning("Solver returned unknown for equivalence check.")
        return False


def are_expressions_equivalent(expr1: z3.ExprRef, expr2: z3.ExprRef, timeout=10000) -> bool:
    """
    Check if two Z3 expressions are logically equivalent.

    Args:
        expr1 (z3.ExprRef): First expression.
        expr2 (z3.ExprRef): Second expression.
        timeout (int): Solver timeout in milliseconds.

    Returns:
        bool: True if expressions are equivalent, False otherwise.
    """
    s = z3.Solver()
    s.set("timeout", timeout)
    # Check if (expr1 AND NOT expr2) OR (NOT expr1 AND expr2) is UNSAT
    equivalence_check = z3.Or(z3.And(expr1, z3.Not(expr2)),
                              z3.And(expr2, z3.Not(expr1)))
    s.add(equivalence_check)
    result = s.check()
    if result == z3.unsat:
        return True
    elif result == z3.sat:
        return False
    else:
        logger.warning("Solver returned unknown for equivalence check.")
        return False


class AbductionProver(object):

    def __init__(self, system: TransitionSystem, timeout: int = 10000, max_iterations: int = 300):
        """
        Initialize the AbductionProver with a given transition system.

        Args:
            system (TransitionSystem): The transition system to verify.

        var_map = [(x, xp), (y, yp)]
        var_map_rev = [(xp ,x), (yp, y)]
        Attributes:
            var_map: Maps current state variables to next state variables [(x, x')]
            var_map_rev: Maps next state variables to current state variables [(x'
        """
        self.sts = system
        self.var_map = list(zip(self.sts.variables, self.sts.prime_variables))
        self.var_map_rev = list(zip(self.sts.prime_variables, self.sts.variables))
        # self.var_map = []
        # self.var_map_rev = []
        #for i in range(len(self.sts.variables)):
        #    self.var_map.append((self.sts.variables[i], self.sts.prime_variables[i]))
        #    self.var_map_rev.append((self.sts.prime_variables[i], self.sts.variables[i]))

    def check_inductiveness(self, inv: z3.ExprRef) -> Tuple[bool, Optional[z3.ModelRef]]:
        """
        Check if the candidate invariant is inductive.

        An invariant I is inductive if:
        I ∧ T → I'
        (where I' is I with all variables primed)

        Args:
            inv: Candidate invariant formula

        Returns:
            Tuple containing:
            - Boolean indicating if inv is inductive
            - If not inductive, a counterexample model; otherwise None
        """
        # Substitute variables in inv to their primed counterparts for I'
        inv_prime = z3.substitute(inv, self.var_map)

        # Check if I ∧ T → I' is valid (equivalent to checking if I ∧ T ∧ ¬I' is unsat)
        s = z3.Solver()
        # s.set("timeout", 10000)  # Set a timeout to prevent long solving times
        s.add(inv)
        s.add(self.sts.trans)
        s.add(z3.Not(inv_prime))

        result = s.check()
        if result == z3.unsat:
            return True, None
        elif result == z3.sat:
            return False, s.model()
        else:
            logger.warning("Solver returned unknown for inductiveness check.")
            return False, None

    def strengthen_from_cti(self, inv: z3.ExprRef, cti: z3.ModelRef) -> z3.ExprRef:
        """
        Strengthen the invariant using a counterexample to inductiveness.

        Args:
            inv: Current candidate invariant
            cti: Counterexample model showing non-inductiveness

        Returns:
            Strengthened invariant formula
        """
        # Extract assignments for current state variables from CTI
        pre_state_constraints = []
        for v in self.sts.variables:
            if v in cti:
                pre_state_constraints.append(v == cti[v])

        pre_state = z3.And(*pre_state_constraints) if pre_state_constraints else z3.BoolVal(True)

        # Extract assignments for next state variables from CTI
        post_state_constraints = []
        for v in self.sts.prime_variables:
            if v in cti:
                post_state_constraints.append(v == cti[v])

        post_state = z3.And(*post_state_constraints) if post_state_constraints else z3.BoolVal(True)
        # Substitute primed variables back to current variables for post conditions
        post_state_substituted = z3.substitute(post_state, self.var_map_rev)

        # Formulate the pre-condition and post-condition
        pre_cond = z3.And(inv, pre_state)
        post_cond = z3.substitute(inv, self.var_map_rev)

        # Incorporate the transition relati on to ensure strengthening considers transitions
        # FIXME: should we do this?...
        combined_pre_cond = z3.And(pre_cond, self.sts.trans)

        # Use abduction to find ψ such that:
        # combined_pre_cond ∧ ψ → post_cond

        # FIXME: should this function take sts.trans into consideration

        strengthening = qe_abduce(combined_pre_cond, post_cond)
        # print("stren ", strengthening)
        # logger.debug("Strengthening condition from abduction: {}".format(strengthening))
        if strengthening is None:
            # If abduction fails, exclude just the CTI point
            strengthening = z3.Not(pre_state)
            logger.debug("Abduction failed. Excluding CTI by strengthening with ¬pre_state.")

        # Combine the strengthening condition with the current invariant
        new_inv = z3.And(inv, strengthening)
        # Simplify the new invariant for better readability and performance
        new_inv = z3.simplify(new_inv)
        logger.debug(f"New invariant after strengthening: {new_inv}")
        return new_inv

    def verify_safety(self, inv: z3.ExprRef) -> Tuple[bool, Optional[z3.ModelRef]]:
        """
        Verify that the invariant proves the safety property.

        Checks:
            1. init → inv        (Initiation)
            2. inv ∧ T → inv'    (Inductiveness)
            3. inv → post        (Safety)

        Returns:
            Tuple containing:
            - Boolean indicating if inv proves safety
            - Counterexample model if verification fails, None otherwise
        """
        s = z3.Solver()
        # s.set("timeout", 10000)  # Set a timeout to prevent long solving times

        # Check initiation
        s.push()
        s.add(self.sts.init)
        s.add(z3.Not(inv))
        if s.check() == z3.sat:
            logger.debug("Initialization does not imply the invariant.")
            return False, s.model()
        s.pop()

        # Check Safety: inv → post
        s.push()
        s.add(inv)
        s.add(z3.Not(self.sts.post))
        if s.check() == z3.sat:
            logger.debug("Invariant does not imply the safety post-condition.")
            return False, s.model()
        s.pop()

        return True, None

    def invgen(self) -> Optional[z3.ExprRef]:
        """
        Generate an inductive invariant using abduction-based refinement.

        The algorithm:
        1. Start with post-condition as candidate
        2. While candidate is not inductive:
           - Find counterexample to inductiveness (CTI)
           - Use abduction to strengthen candidate to eliminate CTI
        3. Return inductive invariant if found

        Returns:
            Inductive invariant formula if found, None otherwise
        """
        inv = self.sts.post
        max_iterations = 300  # Prevent infinite loops
        iteration = 0

        logger.info("Starting invariant generation...")
        while iteration < max_iterations:
            # Check if current candidate proves safety
            logger.debug(f"Iteration {iteration}: Current invariant: {inv}")
            safe, cex = self.verify_safety(inv)
            if not safe:
                logger.info(f"Safety check failed. Counterexample: {cex}")
                return None

            # Check inductiveness
            inductive, cti = self.check_inductiveness(inv)
            if inductive:
                logger.info("Found inductive invariant!")
                return inv

            if cti is None:
                logger.warning("Counterexample to inductiveness (CTI) is None despite inductiveness check failing.")
                return None

            # Strengthen invariant using CTI
            logger.info(f"Strengthening invariant using CTI: {cti}")
            new_inv = self.strengthen_from_cti(inv, cti)

            # Check if the invariant has been strengthened meaningfully
            if are_expressions_equivalent(new_inv, inv):
                # if not check_entailment(new_inv, inv):
                logger.warning("Failed to strengthen invariant; no progress made.")
                return None

            inv = new_inv
            iteration += 1

        logger.warning("Max iterations reached")
        return None

    def solve(self) -> Tuple[bool, Optional[z3.ExprRef]]:
        """
        Verify the system using abductive invariant generation.

        Returns:
            Tuple containing:
            - Boolean indicating if system is safe
            - Inductive invariant proving safety if safe, None otherwise
        """
        inv = self.invgen()
        if inv is not None:
            logger.info("Verification succeeded. System is safe.")
            return True, inv
        logger.info("Verification failed. System is unsafe or invariant generation did not succeed.")
        return False, None
