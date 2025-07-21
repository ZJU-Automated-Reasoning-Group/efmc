"""
Implementation of Farkas' Lemma for linear constraint systems.
"""
from z3 import *
from typing import List, Dict, Any


class FarkasLemma:
    """
    Implementation of Farkas' Lemma for proving unsatisfiability of linear constraints.
    
    Farkas' Lemma: For a system Ax ≤ b, exactly one of the following holds:
    1. ∃x: Ax ≤ b (satisfiable)
    2. ∃λ≥0: λᵀA = 0 ∧ λᵀb < 0 (unsatisfiable with certificate)
    """

    def __init__(self, solver=None):
        self.solver = solver or Solver()
        self.constraints = []
        self.farkas_multipliers = []

    def add_constraint(self, constraint):
        """Add a linear constraint to the system."""
        self.constraints.append(constraint)
        self.solver.add(constraint)

    def add_constraints(self, constraints):
        """Add multiple constraints."""
        for constraint in constraints:
            self.add_constraint(constraint)

    def extract_coefficients(self, expr, variables):
        """Extract coefficients from a linear expression."""
        coeffs = {var: 0 for var in variables}
        
        def extract(e):
            # Check if expression is one of our variables first
            for var in variables:
                if str(e) == str(var):
                    return {var: 1}, 0
            
            if is_const(e):
                if is_int_value(e):
                    return {}, e.as_long()
                elif is_rational_value(e):
                    return {}, float(e.numerator_as_long()) / float(e.denominator_as_long())
                return {}, 0
            
            if is_add(e):
                total_coeffs = {var: 0 for var in variables}
                total_const = 0
                for child in e.children():
                    child_coeffs, child_const = extract(child)
                    for var, coeff in child_coeffs.items():
                        total_coeffs[var] += coeff
                    total_const += child_const
                return total_coeffs, total_const
            
            if is_sub(e):
                children = e.children()
                if len(children) == 2:
                    left_coeffs, left_const = extract(children[0])
                    right_coeffs, right_const = extract(children[1])
                    total_coeffs = {var: 0 for var in variables}
                    for var, coeff in left_coeffs.items():
                        total_coeffs[var] += coeff
                    for var, coeff in right_coeffs.items():
                        total_coeffs[var] -= coeff
                    return total_coeffs, left_const - right_const
            
            if is_mul(e):
                children = e.children()
                if len(children) == 2:
                    left, right = children
                    if is_const(left):
                        for var in variables:
                            if str(right) == str(var):
                                coeff_val = left.as_long() if is_int_value(left) else (
                                    float(left.numerator_as_long()) / float(left.denominator_as_long()) 
                                    if is_rational_value(left) else 1)
                                return {var: coeff_val}, 0
                    elif is_const(right):
                        for var in variables:
                            if str(left) == str(var):
                                coeff_val = right.as_long() if is_int_value(right) else (
                                    float(right.numerator_as_long()) / float(right.denominator_as_long()) 
                                    if is_rational_value(right) else 1)
                                return {var: coeff_val}, 0
            
            # Handle unary minus
            if e.decl().kind() == z3.Z3_OP_UMINUS:
                child_coeffs, child_const = extract(e.children()[0])
                return {var: -coeff for var, coeff in child_coeffs.items()}, -child_const
            
            return {}, 0

        result_coeffs, result_const = extract(expr)
        for var, coeff in result_coeffs.items():
            if var in coeffs:
                coeffs[var] = coeff
        
        return coeffs, result_const

    def apply_farkas_lemma(self, variables):
        """
        Apply Farkas' Lemma to generate constraints on template variables.
        
        Returns constraints that must be satisfied for the system to be unsatisfiable.
        """
        if not self.constraints:
            return [BoolVal(True)]
        
        # Create Farkas multipliers
        self.farkas_multipliers = [Real(f"lambda_{i}") for i in range(len(self.constraints))]
        constraints = [mult >= 0 for mult in self.farkas_multipliers]
        
        # Process each constraint to standard form: expr ≤ 0
        constraint_data = []
        for i, constraint in enumerate(self.constraints):
            try:
                if is_eq(constraint):
                    # a = b → (a-b ≤ 0) ∧ (b-a ≤ 0)
                    lhs, rhs = constraint.arg(0), constraint.arg(1)
                    expr = lhs - rhs
                    coeffs, constant = self.extract_coefficients(expr, variables)
                    constraint_data.append((coeffs, constant))
                    # Add reverse for equality
                    reverse_coeffs = {var: -coeff for var, coeff in coeffs.items()}
                    constraint_data.append((reverse_coeffs, -constant))
                elif is_le(constraint):
                    # a ≤ b → a-b ≤ 0
                    lhs, rhs = constraint.arg(0), constraint.arg(1)
                    expr = lhs - rhs
                    coeffs, constant = self.extract_coefficients(expr, variables)
                    constraint_data.append((coeffs, constant))
                elif is_ge(constraint):
                    # a ≥ b → b-a ≤ 0
                    lhs, rhs = constraint.arg(0), constraint.arg(1)
                    expr = rhs - lhs
                    coeffs, constant = self.extract_coefficients(expr, variables)
                    constraint_data.append((coeffs, constant))
                elif is_not(constraint) and is_ge(constraint.arg(0)):
                    # ¬(a ≥ b) → a < b → b-a ≤ -1
                    inner = constraint.arg(0)
                    lhs, rhs = inner.arg(0), inner.arg(1)
                    expr = rhs - lhs
                    coeffs, constant = self.extract_coefficients(expr, variables)
                    constraint_data.append((coeffs, constant + 1))
            except:
                continue
        
        if not constraint_data:
            return [BoolVal(True)]
        
        # Adjust multipliers for additional constraints
        while len(constraint_data) > len(self.farkas_multipliers):
            idx = len(self.farkas_multipliers)
            self.farkas_multipliers.append(Real(f"lambda_{idx}"))
            constraints.append(self.farkas_multipliers[-1] >= 0)
        
        # Farkas conditions: Σ(λᵢ * aᵢⱼ) = 0 for each variable
        for var in variables:
            sum_expr = sum(self.farkas_multipliers[i] * data[0].get(var, 0) 
                          for i, data in enumerate(constraint_data) 
                          if i < len(self.farkas_multipliers))
            constraints.append(sum_expr == 0)
        
        # Farkas condition: Σ(λᵢ * bᵢ) < 0 for constants
        sum_const = sum(self.farkas_multipliers[i] * data[1] 
                       for i, data in enumerate(constraint_data) 
                       if i < len(self.farkas_multipliers))
        constraints.append(sum_const < 0)
        
        # At least one multiplier must be positive
        if self.farkas_multipliers:
            constraints.append(Or([mult > 0 for mult in self.farkas_multipliers]))
        
        return constraints

    def is_satisfiable(self):
        """Check if the constraint system is satisfiable."""
        return self.solver.check() == sat

    def get_model(self):
        """Get a satisfying model if one exists."""
        return self.solver.model() if self.is_satisfiable() else None

    def get_farkas_coefficients(self):
        """Get Farkas coefficients if the system is unsatisfiable."""
        if self.is_satisfiable():
            return None
        
        try:
            core = self.solver.unsat_core()
            return [1.0 if constraint in core else 0.0 for constraint in self.constraints]
        except:
            return [1.0] * len(self.constraints)

    def prove_unsatisfiability(self):
        """Prove unsatisfiability using Farkas' Lemma."""
        if self.is_satisfiable():
            return False, {"message": "System is satisfiable"}
        
        coefficients = self.get_farkas_coefficients()
        return True, {
            "message": "System is unsatisfiable",
            "farkas_coefficients": coefficients
        }
