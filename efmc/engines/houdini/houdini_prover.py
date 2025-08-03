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
from efmc.utils.verification_utils import VerificationResult
from efmc.utils.z3_expr_utils import get_variables


def get_selector_var(idx: int) -> z3.ExprRef:
    """Create a temp symbol using the given index"""
    return z3.Bool("SEL_{}".format(idx))


def prime(exp: z3.ExprRef) -> z3.ExprRef:
    """Replace all symbols in the formula with their primed version"""
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
        if self.check_inductive(self.sts.post):
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
        lemmas: List[z3.ExprRef] = [self.sts.post]

        # Add existing invariants if available
        if hasattr(self.sts, 'invariants') and self.sts.invariants:
            lemmas.extend(self.sts.invariants)

        # Add bounds for integer variables
        for var in self.sts.variables:
            if var.sort() == z3.IntSort():
                lemmas.append(var >= 0)

        # Add relationships between variables
        for i, var1 in enumerate(self.sts.variables):
            for var2 in self.sts.variables[i + 1:]:
                if var1.sort() == var2.sort():
                    lemmas.extend([var1 <= var2, var1 >= var2])

        self.logger.info(f"Generated {len(lemmas)} candidate lemmas")
        return lemmas

    def check_inductive(self, formula: z3.ExprRef) -> bool:
        """Check if a formula is inductive"""
        s = z3.Solver()
        primed = z3.substitute(formula, list(zip(self.sts.variables, self.sts.prime_variables)))

        # Check: Init => formula
        s.push()
        s.add(self.sts.init)
        s.add(z3.Not(formula))
        if s.check() != z3.unsat:
            s.pop()
            return False
        s.pop()

        # Check: formula ∧ trans => formula'
        s.push()
        s.add(formula)
        s.add(self.sts.trans)
        s.add(z3.Not(primed))
        result = s.check() == z3.unsat
        s.pop()
        return result


def check_invariant(sts: TransitionSystem, inv: z3.ExprRef, inv_prime: z3.ExprRef) -> bool:
    """Check if invariant is valid"""
    s = z3.Solver()
    
    # Check initiation: init => inv
    s.push()
    s.add(sts.init)
    s.add(z3.Not(inv))
    if s.check() != z3.unsat:
        s.pop()
        return False
    s.pop()
    
    # Check consecution: inv ∧ trans => inv'
    s.push()
    s.add(inv)
    s.add(sts.trans)
    s.add(z3.Not(inv_prime))
    result = s.check() == z3.unsat
    s.pop()
    return result


def demo_houdini() -> None:
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
    result = prover.solve(timeout=10)
    
    status = "TIMED OUT" if result.timed_out else "SAFE" if result.is_safe else "UNSAFE" if result.is_unsafe else "UNKNOWN"
    print(f"Simple demo: {status}")
    if result.is_safe:
        print(f"Invariant: {result.invariant}")


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    demo_houdini()