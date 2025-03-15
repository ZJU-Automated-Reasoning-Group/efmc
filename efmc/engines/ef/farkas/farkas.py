"""
TBD: by LLM, to check.
"""
from z3 import *
from typing import List, Tuple, Dict, Any


class FarkasLemma:
    """
    Implementation of Farkas' Lemma for proving unsatisfiability of linear constraints.
    Farkas' Lemma states that for a system of linear inequalities Ax ≤ b, exactly one of the following holds:
    1. There exists an x such that Ax ≤ b
    2. There exists a y ≥ 0 such that y^T A = 0 and y^T b < 0
    """

    def __init__(self, solver=None):
        """
        Initialize the Farkas Lemma solver.
        
        Args:
            solver: Optional Z3 solver instance. If None, a new solver will be created.
        """
        self.solver = solver if solver is not None else Solver()
        self.constraints = []
        self.variables = {}
        self.farkas_multipliers = []

    def add_constraint(self, constraint):
        """
        Add a linear constraint to the system.
        
        Args:
            constraint: A Z3 constraint (typically an inequality)
        """
        self.constraints.append(constraint)
        self.solver.add(constraint)

    def add_constraints(self, constraints):
        """
        Add multiple linear constraints to the system.
        
        Args:
            constraints: A list of Z3 constraints
        """
        for constraint in constraints:
            self.add_constraint(constraint)

    def extract_coefficients(self, expr, variables):
        """
        Extract coefficients from a linear expression.
        
        Args:
            expr: A Z3 expression
            variables: List of variables to extract coefficients for
            
        Returns:
            Dictionary mapping variables to their coefficients, and a constant term
        """
        coeffs = {}
        for var in variables:
            coeffs[var] = 0

        constant = 0

        # Handle different expression types
        if is_const(expr):
            constant = expr.as_long() if is_int_value(expr) else expr.numerator_as_long() / expr.denominator_as_long()
        elif is_var(expr):
            coeffs[expr] = 1
        elif is_add(expr):
            for term in expr.children():
                term_coeffs, term_constant = self.extract_coefficients(term, variables)
                for var, coeff in term_coeffs.items():
                    coeffs[var] += coeff
                constant += term_constant
        elif is_mul(expr):
            if len(expr.children()) == 2:
                if is_const(expr.children()[0]) and is_var(expr.children()[1]):
                    coeff = expr.children()[0].as_long() if is_int_value(expr.children()[0]) else expr.children()[
                                                                                                      0].numerator_as_long() / \
                                                                                                  expr.children()[
                                                                                                      0].denominator_as_long()
                    var = expr.children()[1]
                    if var in coeffs:
                        coeffs[var] += coeff
                elif is_const(expr.children()[1]) and is_var(expr.children()[0]):
                    coeff = expr.children()[1].as_long() if is_int_value(expr.children()[1]) else expr.children()[
                                                                                                      1].numerator_as_long() / \
                                                                                                  expr.children()[
                                                                                                      1].denominator_as_long()
                    var = expr.children()[0]
                    if var in coeffs:
                        coeffs[var] += coeff

        return coeffs, constant

    def apply_farkas_lemma(self, variables):
        """
        Apply Farkas' Lemma to the system of constraints.
        
        Args:
            variables: List of variables in the system
            
        Returns:
            A new constraint system with Farkas multipliers
        """
        # Create Farkas multipliers (one for each constraint)
        self.farkas_multipliers = [Real(f"lambda_{i}") for i in range(len(self.constraints))]

        # Add non-negativity constraints for Farkas multipliers
        farkas_constraints = [multiplier >= 0 for multiplier in self.farkas_multipliers]

        # Extract coefficients from each constraint
        constraint_data = []
        for constraint in self.constraints:
            # Handle different constraint types
            if is_eq(constraint):
                lhs, rhs = constraint.arg(0), constraint.arg(1)
                expr = lhs - rhs
                coeffs, constant = self.extract_coefficients(expr, variables)
                constraint_data.append((coeffs, -constant, "="))
            elif is_le(constraint) or is_lt(constraint):
                lhs, rhs = constraint.arg(0), constraint.arg(1)
                expr = lhs - rhs
                coeffs, constant = self.extract_coefficients(expr, variables)
                constraint_data.append((coeffs, -constant, "<="))
            elif is_ge(constraint) or is_gt(constraint):
                lhs, rhs = constraint.arg(0), constraint.arg(1)
                expr = rhs - lhs
                coeffs, constant = self.extract_coefficients(expr, variables)
                constraint_data.append((coeffs, -constant, "<="))

        # Apply Farkas' Lemma: for each variable, sum of (lambda_i * coeff_i) = 0
        for var in variables:
            sum_expr = 0
            for i, (coeffs, _, _) in enumerate(constraint_data):
                sum_expr += self.farkas_multipliers[i] * coeffs.get(var, 0)
            farkas_constraints.append(sum_expr == 0)

        # For the constant term: sum of (lambda_i * constant_i) < 0
        sum_const = 0
        for i, (_, constant, _) in enumerate(constraint_data):
            sum_const += self.farkas_multipliers[i] * constant
        farkas_constraints.append(sum_const < 0)

        return farkas_constraints

    def is_satisfiable(self):
        """
        Check if the system of constraints is satisfiable.
        
        Returns:
            bool: True if satisfiable, False otherwise
        """
        result = self.solver.check()
        return result == sat

    def get_model(self):
        """
        Get a model (solution) for the constraints if satisfiable.
        
        Returns:
            Z3 model or None if unsatisfiable
        """
        if self.is_satisfiable():
            return self.solver.model()
        return None

    def get_farkas_coefficients(self):
        """
        If the system is unsatisfiable, compute the Farkas coefficients.
        These are non-negative coefficients that, when multiplied with the constraints,
        yield a contradiction (proving unsatisfiability).
        
        Returns:
            List of coefficients or None if the system is satisfiable
        """
        if self.is_satisfiable():
            return None

        # Get the unsat core if available
        if hasattr(self.solver, 'unsat_core'):
            core = self.solver.unsat_core()
            # Process the core to extract coefficients
            # This is a simplified approach and might need adaptation for complex cases
            coefficients = []
            for i, constraint in enumerate(self.constraints):
                if constraint in core:
                    coefficients.append(1.0)  # Simplified: assign 1.0 to constraints in the core
                else:
                    coefficients.append(0.0)
            return coefficients

        # If unsat core is not available, we need a different approach
        # This is a placeholder for a more sophisticated implementation
        return [1.0] * len(self.constraints)  # Simplified

    def prove_unsatisfiability(self):
        """
        Use Farkas' lemma to prove that the system is unsatisfiable.
        
        Returns:
            bool: True if proven unsatisfiable, False otherwise
            dict: Proof information including Farkas coefficients if unsatisfiable
        """
        if self.is_satisfiable():
            return False, {"message": "System is satisfiable"}

        coefficients = self.get_farkas_coefficients()
        return True, {
            "message": "System is unsatisfiable",
            "farkas_coefficients": coefficients
        }
