"""
Houdini algorithm for invariant inference

This module implements the Houdini algorithm for finding maximal inductive invariants,
based on the paper by Flanagan and Leino: "Houdini, an Annotation Assistant for ESC/Java".

Modified from https://github.com/sosy-lab/java-smt/blob/d05b4c8eeb3424be20cc1d9553eaffae81898857/src/org/sosy_lab/java_smt/example/HoudiniApp.java
"""
import logging
from typing import List
import z3

from efmc.sts import TransitionSystem
from efmc.utils.z3_expr_utils import get_variables
from efmc.utils.verification_utils import VerificationResult

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
    """Houdini-based invariant inference engine"""
    
    def __init__(self, system: TransitionSystem):
        """Initialize with a transition system"""
        self.sts = system
        self.logger = logging.getLogger(__name__)

    def houdini(self, lemmas: List[z3.ExprRef]):
        """Find the maximal inductive subset for the given lemmas.
    
        Args:
            lemmas: List of candidate invariant expressions to check
    
        Returns:
            dict: Dictionary mapping indices to lemmas that form the maximal inductive subset
        """
        annotated = []
        annotated_primes = []
        indexed = {}
        
        self.logger.info(f"Starting Houdini algorithm with {len(lemmas)} candidate lemmas")
        
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
        
        while prover.check() != z3.unsat:
            iteration += 1
            m = prover.model()
            removed_in_iteration = 0
            
            for i in list(indexed.keys()):
                annotated_prime = annotated_primes[i]
                if z3.is_false(m.eval(annotated_prime)):
                    prover.add(get_selector_var(i))
                    del indexed[i]
                    removed_in_iteration += 1
            
            self.logger.info(f"Iteration {iteration}: Removed {removed_in_iteration} lemmas, {len(indexed)}/{initial_count} remaining")
        
        self.logger.info(f"Houdini completed after {iteration} iterations with {len(indexed)}/{initial_count} lemmas remaining")
        return indexed

    def solve(self) -> VerificationResult:
        """Main solving procedure.
        
        Returns:
            VerificationResult: Object containing verification result and related data
        """
        # First check if post-condition itself is inductive
        if self.check_inductive(self.sts.post):
            self.logger.info("Post-condition is already inductive")
            return VerificationResult(True, self.sts.post)
    
        # Generate candidate lemmas
        lemmas = self.generate_candidate_lemmas()
        
        # Run Houdini algorithm
        result = self.houdini(lemmas)
        
        if result:
            # Construct final invariant from remaining lemmas
            inv = z3.And(*result.values())
            if self.verify_invariant(inv):
                self.logger.info("Found inductive invariant")
                return VerificationResult(True, inv)
        
        self.logger.info("Could not find inductive invariant")
        return VerificationResult(False, None)
    
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
            for var2 in self.sts.variables[i+1:]:
                if var1.sort() == var2.sort():
                    lemmas.append(var1 <= var2)
                    lemmas.append(var1 >= var2)
        
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
        if s.check() == z3.sat:
            return False
        s.pop()
        
        # Check: formula ∧ trans => formula'
        s.push()
        s.add(formula)
        s.add(self.sts.trans)
        s.add(z3.Not(primed))
        if s.check() == z3.sat:
            return False
        s.pop()
        
        return True

    def verify_invariant(self, inv: z3.ExprRef) -> bool:
        """Verify that an invariant proves the safety property"""
        s = z3.Solver()
        
        # Check initiation
        s.push()
        s.add(self.sts.init)
        s.add(z3.Not(inv))
        if s.check() == z3.sat:
            return False
        s.pop()
        
        # Check inductiveness
        s.push()
        primed = z3.substitute(inv, list(zip(self.sts.variables, self.sts.prime_variables)))
        s.add(inv)
        s.add(self.sts.trans)
        s.add(z3.Not(primed))
        if s.check() == z3.sat:
            return False
        s.pop()
        
        # Check safety
        s.push()
        s.add(inv)
        s.add(z3.Not(self.sts.post))
        if s.check() == z3.sat:
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
    result = prover.solve()
    print(f"Verification result: {result}")

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
    
    prover = HoudiniProver(sts)
    result = prover.solve()
    print(f"Verification result: {result}")

if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    print("Running simple Houdini demo:")
    demo_houdini()
    print("\nRunning complex Houdini demo:")
    demo_houdini_complex()
