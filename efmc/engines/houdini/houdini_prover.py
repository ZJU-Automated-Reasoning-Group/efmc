"""
Houdini algorithm for invariant inference

This module implements the Houdini algorithm for finding maximal inductive invariants,
based on the paper by Flanagan and Leino: "Houdini, an Annotation Assistant for ESC/Java".

Modified from https://github.com/sosy-lab/java-smt/blob/d05b4c8eeb3424be20cc1d9553eaffae81898857/src/org/sosy_lab/java_smt/example/HoudiniApp.java
"""
import logging
from typing import List, Optional
import z3
import time  # Add import for time

from efmc.sts import TransitionSystem
from efmc.utils.z3_expr_utils import get_variables
from efmc.utils.verification_utils import VerificationResult, check_invariant

logger = logging.getLogger(__name__)


def get_selector_var(idx: int):
    """Create a temp symbol using the given index"""
    return z3.Bool("SEL_{}".format(idx))


def prime(exp: z3.ExprRef):
    """
    traverse the formula and replace all symbols in the formula with their primed version
    :param exp:
    :return: a new formula
    """
    variables = get_variables(exp)
    substitutions = []
    for v in variables:
        sort = v.sort()
        if z3.is_bv_sort(sort):
            substitutions.append((v, z3.BitVec(f"{v}_p", sort.size())))
        elif sort == z3.RealSort():
            substitutions.append((v, z3.Real(f"{v}_p")))
        else:  # default to Int
            substitutions.append((v, z3.Int(f"{v}_p")))
    return z3.substitute(exp, substitutions)


class HoudiniProver:
    """Houdini-based invariant inference engine
    
    This class implements the Houdini algorithm for finding maximal inductive invariants.
    It supports timeouts to prevent the algorithm from running too long on complex problems.
    """

    def __init__(self, system: TransitionSystem):
        """Initialize with a transition system"""
        self.sts = system
        self.logger = logging.getLogger(__name__)

    def houdini(self, lemmas: List[z3.ExprRef], timeout=None):
        """Find the maximal inductive subset for the given lemmas.
    
        Args:
            lemmas: List of candidate invariant expressions to check
            timeout: Maximum execution time in seconds (None for no timeout)
    
        Returns:
            dict: Dictionary mapping indices to lemmas that form the maximal inductive subset
                 Returns None if the algorithm times out
        """
        annotated = []
        annotated_primes = []
        indexed = {}
        
        start_time = time.time()  # Record start time for timeout checking

        self.logger.info(f"Starting Houdini algorithm with {len(lemmas)} candidate lemmas" + 
                        (f" (timeout: {timeout}s)" if timeout else ""))

        # Create primed versions and selector variables
        for i in range(len(lemmas)):
            lemma = lemmas[i]
            # Use the transition system's variable mapping for priming
            primed = z3.substitute(lemma, list(zip(self.sts.variables, self.sts.prime_variables)))
            annotated.append(z3.Or(lemma, get_selector_var(i)))
            annotated_primes.append(z3.Or(primed, get_selector_var(i)))
            indexed[i] = lemma

        prover = z3.Solver()
        prover.add(self.sts.trans)  # Add transition relation
        prover.add(z3.And(annotated))
        prover.add(z3.Not(z3.And(annotated_primes)))

        iteration = 0
        initial_count = len(indexed)
        timed_out = False

        while prover.check() != z3.unsat:
            # Check timeout after each iteration
            if timeout and (time.time() - start_time > timeout):
                self.logger.warning(f"Houdini timed out after {iteration} iterations ({timeout}s)")
                timed_out = True
                break
                
            iteration += 1
            m = prover.model()
            removed_in_iteration = 0

            for i in list(indexed.keys()):
                annotated_prime = annotated_primes[i]
                if z3.is_false(m.eval(annotated_prime)):
                    prover.add(get_selector_var(i))
                    del indexed[i]
                    removed_in_iteration += 1

            self.logger.info(
                f"Iteration {iteration}: Removed {removed_in_iteration} lemmas, {len(indexed)}/{initial_count} remaining")

        # Report on completion
        if timed_out:
            self.logger.warning(f"Houdini did not complete due to timeout after {iteration} iterations")
            return None
        else:
            self.logger.info(
                f"Houdini completed after {iteration} iterations with {len(indexed)}/{initial_count} lemmas remaining")
        
        elapsed_time = time.time() - start_time
        self.logger.info(f"Houdini execution time: {elapsed_time:.2f}s")
        
        return indexed

    def solve(self, timeout: Optional[int] = None) -> VerificationResult:
        """Main solving procedure.
        
        Args:
            timeout: Maximum execution time in seconds (None for no timeout)
            
        Returns:
            VerificationResult: Object containing verification result and related data.
                               If timeout occurs, result will have timed_out=True and is_unknown=True.
        """
        start_time = time.time()
        
        # First check if post-condition itself is inductive
        if self.check_inductive(self.sts.post):
            self.logger.info("Post-condition is already inductive")
            return VerificationResult(True, self.sts.post)

        # Generate candidate lemmas
        lemmas = self.generate_candidate_lemmas()

        # Run Houdini algorithm with timeout
        result = self.houdini(lemmas, timeout)

        # Check if we timed out without finding a solution
        if result is None or (timeout and (time.time() - start_time > timeout)):
            self.logger.warning(f"Solver timed out after {time.time() - start_time:.2f}s")
            return VerificationResult(False, None, is_unknown=True, timed_out=True)

        if result:
            # Construct final invariant from remaining lemmas
            inv = z3.And(*result.values())
            # Use the primed version of the invariant for checking
            inv_primed = z3.substitute(inv, list(zip(self.sts.variables, self.sts.prime_variables)))
            if check_invariant(self.sts, inv, inv_primed):
                self.logger.info("Found inductive invariant")
                return VerificationResult(True, inv)

        self.logger.info("Could not find inductive invariant")
        return VerificationResult(False, None, is_unknown=True)

    def generate_candidate_lemmas(self):
        """Generate candidate lemmas for invariant inference"""
        lemmas = []

        # Add post-condition as a candidate
        lemmas.append(self.sts.post)

        # Add existing invariants from the transition system
        # FIXME: add the field "invariatns" for TransitionSystem
        if hasattr(self.sts, 'invariants') and self.sts.invariants:
            lemmas.extend(self.sts.invariants)

        # Add bounds for integer variables
        for var in self.sts.variables:
            if var.sort() == z3.IntSort():
                # Add simple bounds
                lemmas.append(var >= 0)  # Non-negativity

        # Add equality and inequality relationships between variables
        for i, var1 in enumerate(self.sts.variables):
            for var2 in self.sts.variables[i + 1:]:
                if var1.sort() == var2.sort():
                    lemmas.append(var1 <= var2)
                    lemmas.append(var1 >= var2)

        self.logger.info(f"Generated {len(lemmas)} candidate lemmas")
        return lemmas

    def check_inductive(self, formula: z3.ExprRef) -> bool:
        """Check if a formula is inductive
        
        Args:
            formula: The formula to check for inductiveness
            
        Returns:
            bool: True if formula is inductive, False otherwise
        """
        s = z3.Solver()
        primed = z3.substitute(formula, list(zip(self.sts.variables, self.sts.prime_variables)))

        # Check: Init => formula
        s.push()
        s.add(self.sts.init)
        s.add(z3.Not(formula))
        result = s.check()
        if result == z3.unknown:
            self.logger.warning("Z3 solver returned unknown during initiation check")
            return False
        if result == z3.sat:
            return False
        s.pop()

        # Check: formula ∧ trans => formula'
        s.push()
        s.add(formula)
        s.add(self.sts.trans)
        s.add(z3.Not(primed))
        result = s.check()
        if result == z3.unknown:
            self.logger.warning("Z3 solver returned unknown during consecution check")
            return False
        if result == z3.sat:
            return False
        s.pop()

        return True


def demo_houdini():
    """Demo using a simple transition system"""
    x = z3.Int("x")
    x_prime = z3.Int("x_p")

    sts = TransitionSystem()
    sts.init = x == 0
    sts.trans = x_prime == x + 1
    sts.post = x >= 0
    sts.variables = [x]
    sts.prime_variables = [x_prime]
    sts.all_variables = [x, x_prime]
    sts.initialized = True

    prover = HoudiniProver(sts)
    result = prover.solve(timeout=10)  # Set a 10 second timeout
    
    if result.timed_out:
        print(f"Verification timed out")
    elif result.is_safe:
        print(f"System is SAFE. Found invariant: {result.invariant}")
    elif result.is_unsafe:
        print(f"System is UNSAFE. Found counterexample.")
    else:
        print(f"Verification result is UNKNOWN")


def demo_houdini_complex():
    """Demo using a more complex transition system with multiple variables"""
    x = z3.Int("x")
    y = z3.Int("y")
    x_prime = z3.Int("x_p")
    y_prime = z3.Int("y_p")

    sts = TransitionSystem()
    sts.init = z3.And(x == 0, y == 0)
    sts.trans = z3.And(x_prime == x + y, y_prime == y + 1)
    sts.post = x >= 0
    sts.variables = [x, y]
    sts.prime_variables = [x_prime, y_prime]
    sts.all_variables = [x, y, x_prime, y_prime]
    sts.initialized = True

    # Add some invariants as hints
    sts.invariants = [y >= 0]

    # Try with different timeouts
    timeouts = [0.1, 1, 20]  # 0.1s (should timeout), 1s, 20s
    
    for t in timeouts:
        print(f"\nRunning with timeout of {t} seconds:")
        prover = HoudiniProver(sts)
        start_time = time.time()
        result = prover.solve(timeout=t)
        elapsed = time.time() - start_time
        
        if result.timed_out:
            print(f"Verification timed out after {elapsed:.2f}s")
        elif result.is_safe:
            print(f"System is SAFE. Found invariant: {result.invariant}")
            print(f"Verification completed in {elapsed:.2f}s")
        elif result.is_unsafe:
            print(f"System is UNSAFE. Found counterexample.")
            print(f"Verification completed in {elapsed:.2f}s")
        else:
            print(f"Verification result is UNKNOWN")
            print(f"Verification completed in {elapsed:.2f}s")


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    print("Running simple Houdini demo:")
    demo_houdini()
    print("\nRunning complex Houdini demo:")
    demo_houdini_complex()
