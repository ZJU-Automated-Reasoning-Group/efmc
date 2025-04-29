"""Inductive Generalization

Counterexample-guided inductive generalization, e.g., using counterexamples to induction (CTI)

I think the CTI can be due to the violation of the following conditions:
1. Initiation: init => inv
2. Inductiveness: inv && trans => inv'
3. Safety: inv => post

Given a candidate invariant, we can check if it is a CTI by checking the above conditions. For refinement, the key challenge is how to "learn" the correct invariant from the counterexamples,
e.g., adding more lemmas to the candidate invariant (via disjuncts, conjuncts, etc.).

Some interesting things / notions: 
- A is inductive relative to B, if ....?
- A and B are mutual inductive, if ..?


Existing strategies for generalization in the literature:
- Craig interpolant
- Abductive inference
- ...


Many SMT-based verification algorithms benefit from generalization (or we should say, the generalization is a key component of the verification algorithm):
- IC3/DPR
- CEGAR with Craig interpolant
- Trace abstraction
- ...

How to design new generalization strategies?


FIXME: by LLM, to check if the generalization is correct
"""

import logging
import z3
from typing import List, Tuple, Optional, Dict, Set

from efmc.utils.z3_solver_utils import is_entail, is_sat, is_equiv
from efmc.utils.z3_expr_utils import get_variables, negate, get_atoms, big_and
from efmc.sts import TransitionSystem

logger = logging.getLogger(__name__)


class InductiveGeneralizer:
    """Main class for inductive generalization
    
    
    
    """

    def __init__(self, sts: TransitionSystem):
        self.sts = sts
        self.logger = logging.getLogger(__name__)
        self.timeout = 10000  # Default timeout in milliseconds

    def set_timeout(self, timeout_ms: int):
        """Set the timeout for SMT solver calls"""
        self.timeout = timeout_ms

    def check_invariant(self, inv: z3.ExprRef) -> Tuple[bool, Optional[str], Optional[z3.ModelRef]]:
        """
        Check if a candidate invariant satisfies all three conditions:
        1. Initiation: init => inv
        2. Inductiveness: inv && trans => inv'
        3. Safety: inv => post
        
        Returns:
            - Boolean indicating if inv is a valid invariant
            - If not valid, a string indicating which condition failed
            - If not valid, a counterexample model
        """
        # Check initiation
        if not is_entail(self.sts.init, inv):
            s = z3.Solver()
            s.set("timeout", self.timeout)
            s.add(self.sts.init, z3.Not(inv))
            if s.check() == z3.sat:
                return False, "initiation", s.model()

        # Check inductiveness
        inv_prime = z3.substitute(inv, list(zip(self.sts.variables, self.sts.prime_variables)))
        if not is_entail(z3.And(inv, self.sts.trans), inv_prime):
            s = z3.Solver()
            s.set("timeout", self.timeout)
            s.add(inv, self.sts.trans, z3.Not(inv_prime))
            if s.check() == z3.sat:
                return False, "inductiveness", s.model()

        # Check safety
        if not is_entail(inv, self.sts.post):
            s = z3.Solver()
            s.set("timeout", self.timeout)
            s.add(inv, z3.Not(self.sts.post))
            if s.check() == z3.sat:
                return False, "safety", s.model()

        return True, None, None

    def get_cti(self, inv: z3.ExprRef) -> Tuple[Optional[str], Optional[z3.ModelRef]]:
        """
        Get a counterexample to induction (CTI) for a candidate invariant.
        
        Returns:
            - A string indicating which condition failed ("initiation", "inductiveness", or "safety")
            - A counterexample model
        """
        valid, condition, model = self.check_invariant(inv)
        if valid:
            return None, None
        return condition, model

    def strengthen_from_cti(self, inv: z3.ExprRef, cti: z3.ModelRef) -> z3.ExprRef:
        """
        Strengthen the invariant by excluding the counterexample state.
        This is a simple but effective strategy for inductive generalization.
        
        Args:
            inv: Current candidate invariant
            cti: Counterexample model
            
        Returns:
            Strengthened invariant formula
        """
        # Extract state constraints from CTI
        state_constraints = []
        for v in self.sts.variables:
            if v in cti:
                state_constraints.append(v == cti[v])

        state = z3.And(*state_constraints) if state_constraints else z3.BoolVal(True)

        # Strengthen by excluding this state
        return z3.simplify(z3.And(inv, z3.Not(state)))

    def weaken_from_cti(self, inv: z3.ExprRef, cti: z3.ModelRef) -> z3.ExprRef:
        """
        Weaken the invariant to include the counterexample state.
        This is useful when the invariant is too strong and violates initiation.
        
        Args:
            inv: Current candidate invariant
            cti: Counterexample model
            
        Returns:
            Weakened invariant formula
        """
        # Extract state constraints from CTI
        state_constraints = []
        for v in self.sts.variables:
            if v in cti:
                state_constraints.append(v == cti[v])

        state = z3.And(*state_constraints) if state_constraints else z3.BoolVal(True)

        # Weaken by including this state
        return z3.simplify(z3.Or(inv, state))

    def generalize_by_dropping_literals(self, inv: z3.ExprRef) -> z3.ExprRef:
        """
        Generalize an invariant by dropping literals that are not necessary for inductiveness.
        This is a common strategy in IC3/PDR algorithms.
        
        Args:
            inv: Current candidate invariant (assumed to be in CNF form)
            
        Returns:
            Generalized invariant formula
        """
        # Get the clauses (assuming inv is in CNF form)
        if inv.decl().kind() == z3.Z3_OP_AND:
            clauses = inv.children()
        else:
            clauses = [inv]

        # Try dropping each clause and check if the result is still inductive
        necessary_clauses = []
        for i, clause in enumerate(clauses):
            # Create a new invariant without this clause
            remaining_clauses = clauses[:i] + clauses[i + 1:]
            if not remaining_clauses:
                # Can't drop the only clause
                necessary_clauses.append(clause)
                continue

            candidate = z3.And(*remaining_clauses) if len(remaining_clauses) > 1 else remaining_clauses[0]

            # Check if the candidate is still inductive
            inv_prime = z3.substitute(candidate, list(zip(self.sts.variables, self.sts.prime_variables)))
            if is_entail(z3.And(candidate, self.sts.trans), inv_prime) and is_entail(candidate, self.sts.post):
                # This clause is not necessary, continue with the reduced invariant
                return self.generalize_by_dropping_literals(candidate)
            else:
                # This clause is necessary
                necessary_clauses.append(clause)

        return z3.And(*necessary_clauses) if len(necessary_clauses) > 1 else necessary_clauses[0]

    def generalize_by_craig_interpolation(self, A: z3.ExprRef, B: z3.ExprRef) -> Optional[z3.ExprRef]:
        """
        Use Craig interpolation to find a formula I such that:
        1. A implies I
        2. I and B are unsatisfiable
        3. I only contains variables common to A and B
        
        This is useful for finding invariants that separate reachable states from unsafe states.
        
        Args:
            A: Formula representing reachable states
            B: Formula representing unsafe states
            
        Returns:
            An interpolant formula, or None if interpolation fails
        """
        try:
            # Check if A and B are unsatisfiable together
            s = z3.Solver()
            s.add(A, B)
            if s.check() == z3.sat:
                self.logger.warning("Cannot compute interpolant: A and B are satisfiable together")
                return None

            # Use Z3's interpolation capability
            # Note: This requires Z3 to be built with interpolation support
            interpolant = z3.Interpolant(A, B)
            return interpolant
        except Exception as e:
            self.logger.warning(f"Interpolation failed: {e}")
            return None

    def generalize_by_abduction(self, pre: z3.ExprRef, post: z3.ExprRef) -> Optional[z3.ExprRef]:
        """
        Use abductive inference to find a formula F such that:
        1. pre and F imply post
        2. F is consistent with pre
        
        This is useful for strengthening invariants to make them inductive.
        
        Args:
            pre: Precondition formula
            post: Postcondition formula
            
        Returns:
            An abduced formula, or None if abduction fails
        """
        # A simple implementation using quantifier elimination
        # Find F such that: pre and F => post, and pre and F is satisfiable

        # Get all variables in pre and post
        vars_pre = get_variables(pre)
        vars_post = get_variables(post)
        all_vars = list(set(vars_pre + vars_post))

        # Create a fresh variable for F
        F = z3.Bool("F")

        # Create the formula: (pre and F => post) and (pre and F is satisfiable)
        formula = z3.And(z3.Implies(z3.And(pre, F), post), z3.And(pre, F))

        # Use quantifier elimination to solve for F
        try:
            # This is a simplified approach and may not work in all cases
            # Real abduction algorithms are more complex
            s = z3.Solver()
            s.add(formula)
            if s.check() == z3.sat:
                model = s.model()
                if F in model:
                    return model[F]
            return None
        except Exception as e:
            self.logger.warning(f"Abduction failed: {e}")
            return None

    def generalize_by_ic3_inductive_generalization(self, clause: z3.ExprRef, inv: z3.ExprRef) -> z3.ExprRef:
        """
        Implement the IC3 inductive generalization algorithm to generalize a clause.
        This tries to drop literals from the clause while maintaining relative inductiveness.
        
        Args:
            clause: The clause to generalize (typically a negated state)
            inv: The current invariant
            
        Returns:
            Generalized clause
        """
        if clause.decl().kind() == z3.Z3_OP_OR:
            literals = clause.children()
        else:
            literals = [clause]

        # Try dropping each literal and check if the result is still inductive relative to inv
        result_literals = list(literals)
        for i, lit in enumerate(literals):
            # Create a candidate without this literal
            candidate_literals = result_literals[:i] + result_literals[i + 1:]
            if not candidate_literals:
                # Can't drop the only literal
                continue

            candidate = z3.Or(*candidate_literals) if len(candidate_literals) > 1 else candidate_literals[0]

            # Check if candidate is inductive relative to inv
            # A clause c is inductive relative to inv if: inv and trans and ¬c' implies ¬c
            # Which is equivalent to: inv and trans and c implies c'
            c_prime = z3.substitute(candidate, list(zip(self.sts.variables, self.sts.prime_variables)))
            if is_entail(z3.And(inv, self.sts.trans, candidate), c_prime):
                # This literal can be dropped
                result_literals = candidate_literals
                # Restart the loop with the new set of literals
                i = -1

        return z3.Or(*result_literals) if len(result_literals) > 1 else result_literals[0]

    def learn_invariant(self, max_iterations: int = 100) -> Optional[z3.ExprRef]:
        """
        Learn an inductive invariant using counterexample-guided refinement.
        
        Args:
            max_iterations: Maximum number of refinement iterations
            
        Returns:
            An inductive invariant if found, None otherwise
        """
        # Start with the post-condition as the initial candidate
        inv = self.sts.post

        for iteration in range(max_iterations):
            self.logger.info(f"Iteration {iteration}: Checking candidate invariant")

            # Check if the candidate is a valid invariant
            valid, condition, cti = self.check_invariant(inv)
            if valid:
                self.logger.info("Found valid invariant")
                return inv

            # Refine the invariant based on the counterexample
            if condition == "initiation":
                self.logger.info("Counterexample to initiation, weakening invariant")
                inv = self.weaken_from_cti(inv, cti)
            elif condition == "inductiveness":
                self.logger.info("Counterexample to inductiveness, strengthening invariant")
                inv = self.strengthen_from_cti(inv, cti)
            elif condition == "safety":
                self.logger.info("Counterexample to safety, invariant cannot ensure safety")
                return None

            # Generalize the invariant
            inv = self.generalize_by_dropping_literals(inv)

        self.logger.warning(f"Exceeded maximum iterations ({max_iterations})")
        return None
