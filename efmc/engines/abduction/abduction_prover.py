"""
Implementation of the following paper:
    Inductive Invariant Generation via Abductive Inference. OOPSLA'13

(TODO: not finished yet)

The algorithm uses abductive inference to strengthen candidate invariants until finding
an inductive invariant that proves the property.
"""

import logging
from typing import Tuple, Optional, Dict

import z3

from efmc.engines.abduction.abduction import qe_abduce
from efmc.sts import TransitionSystem

logger = logging.getLogger(__name__)


class AbductionProver(object):

    def __init__(self, system: TransitionSystem):
        """
        var_map = [(x, xp), (y, yp)]
        var_map_rev = [(xp ,x), (yp, y)]
        Attributes:
            var_map: Maps current state variables to next state variables [(x, x')]
            var_map_rev: Maps next state variables to current state variables [(x'
        """
        self.sts = system
        self.var_map = []
        self.var_map_rev = []
        for i in range(len(self.sts.variables)):
            self.var_map.append((self.sts.variables[i], self.sts.prime_variables[i]))
            self.var_map_rev.append((self.sts.prime_variables[i], self.sts.variables[i]))

    def check_inductiveness(self, inv: z3.ExprRef) -> Tuple[bool, Optional[z3.ModelRef]]:
        """
        Check if the candidate invariant is inductive.

        An invariant I is inductive if:
        I ∧ T → I'  (where I' is I with all variables primed)

        Args:
            inv: Candidate invariant formula

        Returns:
            Tuple containing:
            - Boolean indicating if inv is inductive
            - If not inductive, a counterexample model; otherwise None
        """
        inv_prime = z3.substitute(inv, self.var_map)

        # Check if I ∧ T → I' is valid (equivalent to checking if I ∧ T ∧ ¬I' is unsat)
        s = z3.Solver()
        s.add(inv)
        s.add(self.sts.trans)
        s.add(z3.Not(inv_prime))

        if s.check() == z3.sat:
            return False, s.model()
        return True, None

    def strengthen_from_cti(self, inv: z3.ExprRef, cti: z3.ModelRef) -> z3.ExprRef:
        """
        Strengthen the invariant using a counterexample to inductiveness.

        Args:
            inv: Current candidate invariant
            cti: Counterexample model showing non-inductiveness

        Returns:
            Strengthened invariant formula
        """
        # Extract the pre-state from CTI
        pre_state_constraints = []
        for v in self.sts.variables:
            if v in cti:
                pre_state_constraints.append(v == cti[v])
        pre_state = z3.And(*pre_state_constraints)

        # Extract the post-state from CTI
        post_state_constraints = []
        for v in self.sts.prime_variables:
            if v in cti:
                post_state_constraints.append(v == cti[v])
        post_state = z3.substitute(z3.And(*post_state_constraints), self.var_map_rev)

        # Use abduction to find ψ such that:
        # inv ∧ ψ → inv'
        # where ψ eliminates the CTI
        pre_cond = z3.And(inv, pre_state)
        post_cond = z3.substitute(inv, self.var_map_rev)

        strengthening = qe_abduce(pre_cond, post_cond)
        if strengthening is None:
            # If abduction fails, exclude just the CTI point
            strengthening = z3.Not(pre_state)

        return z3.And(inv, strengthening)

    def verify_safety(self, inv: z3.ExprRef) -> Tuple[bool, Optional[z3.ModelRef]]:
        """
        Verify that the invariant proves the safety property.

        Checks:
        1. init → inv (initiation)
        2. inv → post (safety)

        Returns:
            Tuple containing:
            - Boolean indicating if inv proves safety
            - Counterexample model if verification fails, None otherwise
        """
        s = z3.Solver()

        # Check initiation
        s.push()
        s.add(self.sts.init)
        s.add(z3.Not(inv))
        if s.check() == z3.sat:
            return False, s.model()
        s.pop()

        # Check safety
        s.push()
        s.add(inv)
        s.add(z3.Not(self.sts.post))
        if s.check() == z3.sat:
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
        max_iterations = 100  # Prevent infinite loops
        iteration = 0

        while iteration < max_iterations:
            # Check if current candidate proves safety
            safe, cex = self.verify_safety(inv)
            if not safe:
                logger.info(f"Safety check failed. Counterexample: {cex}")
                return None

            # Check inductiveness
            inductive, cti = self.check_inductiveness(inv)
            if inductive:
                logger.info("Found inductive invariant!")
                return inv

            # Strengthen invariant using CTI
            logger.info(f"Strengthening invariant using CTI: {cti}")
            new_inv = self.strengthen_from_cti(inv, cti)

            # Check if meaningful progress was made
            if new_inv == inv:
                logger.warning("Failed to strengthen invariant")
                return None

            inv = new_inv
            iteration += 1

        logger.warning("Max iterations reached")
        return None

    def verify(self) -> Tuple[bool, Optional[z3.ExprRef]]:
        """
        Verify the system using abductive invariant generation.

        Returns:
            Tuple containing:
            - Boolean indicating if system is safe
            - Inductive invariant proving safety if safe, None otherwise
        """
        inv = self.invgen()
        if inv is not None:
            return True, inv
        return False, None


def demo_abduction_prover():
    """Simple test cases for the abduction-based prover"""

    def create_counter_system() -> TransitionSystem:
        """Create a simple counter system"""
        x = z3.Int('x')
        xp = z3.Int("x'")

        init = x == 0
        trans = xp == x + 1
        post = x <= 10

        return TransitionSystem(
            variables=[x],
            prime_variables=[xp],
            init=init,
            trans=trans,
            post=post
        )

    def create_simple_loop() -> TransitionSystem:
        """Create a simple loop system"""
        x, y = z3.Ints('x y')
        xp, yp = z3.Ints("x' y'")

        init = z3.And(x == 0, y == 0)
        trans = z3.And(xp == x + 1, yp == y + 2)
        post = y <= 2 * x

        return TransitionSystem(
            variables=[x, y],
            prime_variables=[xp, yp],
            init=init,
            trans=trans,
            post=post
        )

    # Test cases
    systems = [
        ("Counter", create_counter_system(), True),
        ("Simple Loop", create_simple_loop(), True)
    ]

    for name, system, expected_safe in systems:
        print(f"\nTesting {name}:")
        prover = AbductionProver(system)
        safe, inv = prover.verify()

        print(f"System is {'safe' if safe else 'unsafe'}")
        print(f"Expected: {'safe' if expected_safe else 'unsafe'}")
        if safe:
            print(f"Inductive invariant: {inv}")

        assert safe == expected_safe, f"Incorrect result for {name}"


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    demo_abduction_prover()

